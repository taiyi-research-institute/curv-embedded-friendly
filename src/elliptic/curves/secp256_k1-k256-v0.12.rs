#![allow(non_snake_case)]
// replace secp256k1 crate by k256 crate
/*
    This file is part of Curv library
    Copyright 2018 by Kzen Networks
    (https://github.com/KZen-networks/curv)
    License MIT: <https://github.com/KZen-networks/curv/blob/master/LICENSE>
*/

// Secp256k1 elliptic curve utility functions (se: https://en.bitcoin.it/wiki/Secp256k1).
//
// In Cryptography utilities, we need to manipulate low level elliptic curve members as Point
// in order to perform operation on them. As the library secp256k1 expose only SecretKey and
// PublicKey, we extend those with simple codecs.
//
// The Secret Key codec: BigInt <> SecretKey
// The Public Key codec: Point <> SecretKey
//

use std::convert::TryFrom;

use k256::elliptic_curve::group::ff::PrimeField;
use k256::elliptic_curve::group::prime::PrimeCurveAffine;
use k256::elliptic_curve::sec1::{FromEncodedPoint, ToEncodedPoint};
use k256::{AffinePoint, EncodedPoint, FieldBytes, ProjectivePoint, Scalar};

use generic_array::GenericArray;
use rand::{thread_rng, Rng};
use serde::{Deserialize, Serialize};
use zeroize::{Zeroize, Zeroizing};

use crate::arithmetic::*;
use super::traits::*;
use crate::elliptic::curves::{Curve, DeserializationError, NotOnCurve, PointCoords};
use crate::BigInt;

lazy_static::lazy_static! {
    static ref GROUP_ORDER: BigInt = BigInt::from_bytes(&GROUP_ORDER_BYTES);

    static ref BASE_POINT2_UNCOMPRESSED: EncodedPoint = {
        let mut g = [0u8; 65];
        g[0] = 0x04;
        g[1..33].copy_from_slice(&BASE_POINT2_X);
        g[33..].copy_from_slice(&BASE_POINT2_Y);
        EncodedPoint::from_bytes(g).unwrap()
    };

    static ref BASE_POINT2: Secp256k1Point = Secp256k1Point {
        purpose: "base_point2",
        ge: PK::from_encoded_point(&BASE_POINT2_UNCOMPRESSED).unwrap(),
    };

    static ref GENERATOR: Secp256k1Point = Secp256k1Point {
        purpose: "generator",
        ge: AffinePoint::generator(),
    };
}

/* X coordinate of a point of unknown discrete logarithm.
Computed using a deterministic algorithm with the generator as input.
See test_base_point2 */
const BASE_POINT2_X: [u8; 32] = [
    0x08, 0xd1, 0x32, 0x21, 0xe3, 0xa7, 0x32, 0x6a, 0x34, 0xdd, 0x45, 0x21, 0x4b, 0xa8, 0x01, 0x16,
    0xdd, 0x14, 0x2e, 0x4b, 0x5f, 0xf3, 0xce, 0x66, 0xa8, 0xdc, 0x7b, 0xfa, 0x03, 0x78, 0xb7, 0x95,
];
const BASE_POINT2_Y: [u8; 32] = [
    0x5d, 0x41, 0xac, 0x14, 0x77, 0x61, 0x4b, 0x5c, 0x08, 0x48, 0xd5, 0x0d, 0xbd, 0x56, 0x5e, 0xa2,
    0x80, 0x7b, 0xcb, 0xa1, 0xdf, 0x0d, 0xf0, 0x7a, 0x82, 0x17, 0xe9, 0xf7, 0xf7, 0xc2, 0xbe, 0x88,
];
const GROUP_ORDER_BYTES: [u8; 32] = [
    0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFE,
    0xBA, 0xAE, 0xDC, 0xE6, 0xAF, 0x48, 0xA0, 0x3B, 0xBF, 0xD2, 0x5E, 0x8C, 0xD0, 0x36, 0x41, 0x41,
];

/// K-256 curve implementation based on [k256] library
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Secp256k1 {}

pub type SK = Scalar;
pub type PK = AffinePoint;

#[derive(Clone, Debug)]
pub struct Secp256k1Scalar {
    #[allow(dead_code)]
    purpose: &'static str,
    /// Zeroizing<SK> wraps SK and zeroize it on drop
    ///
    /// `fe` might be None — special case for scalar being zero
    fe: zeroize::Zeroizing<SK>,
}
#[derive(Clone, Debug, Copy)]
pub struct Secp256k1Point {
    #[allow(dead_code)]
    purpose: &'static str,
    ge: PK,
}

type GE = Secp256k1Point;
type FE = Secp256k1Scalar;

impl Curve for Secp256k1 {
    type Point = GE;
    type Scalar = FE;

    const CURVE_NAME: &'static str = "secp256k1";
}

impl ECScalar for Secp256k1Scalar {
    type Underlying = SK;

    type ScalarLength = typenum::U32;

    fn random() -> Secp256k1Scalar {
        let mut rng = thread_rng();
        let scalar = loop {
            let mut bytes = FieldBytes::default();
            rng.fill(&mut bytes[..]);
            let element = Scalar::from_repr(bytes);
            if bool::from(element.is_some()) {
                break element.unwrap();
            }
        };
        Secp256k1Scalar {
            purpose: "random",
            fe: scalar.into(),
        }
    }

    fn zero() -> Secp256k1Scalar {
        Secp256k1Scalar {
            purpose: "zero",
            fe: Scalar::ZERO.into(),
        }
    }

    fn is_zero(&self) -> bool {
        bool::from(self.fe.is_zero())
    }

    fn from_bigint(n: &BigInt) -> Secp256k1Scalar {
        let curve_order = Secp256k1Scalar::group_order();
        let n_reduced = n
            .modulus(curve_order)
            .to_bytes_array::<32>()
            .expect("n mod curve_order must be equal or less than 32 bytes");
        
        let bytes = FieldBytes::from(n_reduced);
        let scalar = Scalar::from_repr(bytes);

        Secp256k1Scalar {
            purpose: "from_bigint",
            fe: scalar.unwrap().into(),
        }
    }

    fn to_bigint(&self) -> BigInt {
        BigInt::from_bytes(self.fe.to_bytes().as_slice())
    }

    fn serialize(&self) -> GenericArray<u8, Self::ScalarLength> {
        self.fe.to_bytes()
    }

    fn deserialize(bytes: &[u8]) -> Result<Self, DeserializationError> {
        let bytes = <[u8; 32]>::try_from(bytes).or(Err(DeserializationError))?;
        let bytes = FieldBytes::from(bytes);
        let scalar = Scalar::from_repr(bytes);

        if bool::from(scalar.is_some()) {
            Ok(Secp256k1Scalar {
                purpose: "deserialize",
                fe: scalar.unwrap().into(),
            })
        } else {
            Err(DeserializationError)
        }
    }

    fn add(&self, other: &Self) -> Secp256k1Scalar {
        Secp256k1Scalar {
            purpose: "add",
            fe: (*self.fe + *other.fe).into(),
        }
    }

    fn mul(&self, other: &Self) -> Secp256k1Scalar {
        Secp256k1Scalar {
            purpose: "mul",
            fe: (*self.fe * *other.fe).into(),
        }
    }

    fn sub(&self, other: &Self) -> Secp256k1Scalar {
        Secp256k1Scalar {
            purpose: "sub",
            fe: (*self.fe - *other.fe).into(),
        }
    }

    fn neg(&self) -> Self {
        Secp256k1Scalar {
            purpose: "sub",
            fe: (-&*self.fe).into(),
        }
    }

    fn invert(&self) -> Option<Secp256k1Scalar> {
        Some(Secp256k1Scalar {
            purpose: "invert",
            fe: Option::<SK>::from(self.fe.invert())?.into(),
        })
    }

    fn add_assign(&mut self, other: &Self) {
        self.purpose = "add_assign";
        *self.fe += &*other.fe
    }
    fn mul_assign(&mut self, other: &Self) {
        self.purpose = "mul_assign";
        *self.fe *= &*other.fe
    }
    fn sub_assign(&mut self, other: &Self) {
        self.purpose = "sub_assign";
        *self.fe -= &*other.fe
    }

    fn group_order() -> &'static BigInt {
        &GROUP_ORDER
    }

    fn underlying_ref(&self) -> &Self::Underlying {
        &self.fe
    }

    fn underlying_mut(&mut self) -> &mut Self::Underlying {
        &mut self.fe
    }

    fn from_underlying(u: Self::Underlying) -> Secp256k1Scalar {
        Secp256k1Scalar {
            purpose: "from_underlying",
            fe: Zeroizing::new(u),
        }
    }
}

impl PartialEq for Secp256k1Scalar {
    fn eq(&self, other: &Secp256k1Scalar) -> bool {
        self.fe == other.fe
    }
}

impl ECPoint for Secp256k1Point {
    type Scalar = Secp256k1Scalar;
    type Underlying = PK;

    type CompressedPointLength = typenum::U33;
    type UncompressedPointLength = typenum::U65;

    fn zero() -> Secp256k1Point {
        Secp256k1Point {
            purpose: "zero",
            ge: AffinePoint::identity(),
        }
    }

    fn is_zero(&self) -> bool {
        bool::from(self.ge.is_identity())
    }

    fn generator() -> &'static Secp256k1Point {
        &GENERATOR
    }

    fn base_point2() -> &'static Secp256k1Point {
        &BASE_POINT2
    }

    fn from_coords(x: &BigInt, y: &BigInt) -> Result<Secp256k1Point, NotOnCurve> {
        let x_arr = x.to_bytes_array::<32>().ok_or(NotOnCurve)?;
        let y_arr = y.to_bytes_array::<32>().ok_or(NotOnCurve)?;
        let ge = PK::from_encoded_point(&EncodedPoint::from_affine_coordinates(
            &x_arr.into(),
            &y_arr.into(),
            false,
        ));

        if bool::from(ge.is_some()) {
            Ok(Secp256k1Point {
                purpose: "from_coords",
                ge: ge.unwrap(),
            })
        } else {
            Err(NotOnCurve)
        }
    }

    fn x_coord(&self) -> Option<BigInt> {
        let encoded = self.ge.to_encoded_point(false);
        let x = BigInt::from_bytes(encoded.x()?.as_slice());
        Some(x)
    }

    fn y_coord(&self) -> Option<BigInt> {
        let encoded = self.ge.to_encoded_point(false);
        let y = BigInt::from_bytes(encoded.y()?.as_slice());
        Some(y)
    }

    fn coords(&self) -> Option<PointCoords> {
        let encoded = self.ge.to_encoded_point(false);
        let x = BigInt::from_bytes(encoded.x()?.as_slice());
        let y = BigInt::from_bytes(encoded.y()?.as_slice());
        Some(PointCoords { x, y })
    }

    fn serialize_compressed(&self) -> GenericArray<u8, Self::CompressedPointLength> {
        if self.is_zero() {
            *GenericArray::from_slice(&[0u8; 33])
        } else {
            *GenericArray::from_slice(self.ge.to_encoded_point(true).as_ref())
        }
    }

    fn serialize_uncompressed(&self) -> GenericArray<u8, Self::UncompressedPointLength> {
        if self.is_zero() {
            *GenericArray::from_slice(&[0u8; 65])
        } else {
            *GenericArray::from_slice(self.ge.to_encoded_point(false).as_ref())
        }
    }

    fn deserialize(bytes: &[u8]) -> Result<Secp256k1Point, DeserializationError> {
        if bytes == [0; 33] || bytes == [0; 65] {
            Ok(Secp256k1Point {
                purpose: "from_bytes",
                ge: Self::zero().ge,
            })
        } else {
            let encoded = EncodedPoint::from_bytes(bytes).map_err(|_| DeserializationError)?;
            let affine_point = AffinePoint::from_encoded_point(&encoded);

            Ok(Secp256k1Point {
                purpose: "from_bytes",
                ge: affine_point.unwrap(),
            })
        }
    }

    fn check_point_order_equals_group_order(&self) -> bool {
        // This curve has cofactor=1 => any nonzero point has order GROUP_ORDER
        !self.is_zero()
    }

    fn scalar_mul(&self, scalar: &Self::Scalar) -> Secp256k1Point {
        Secp256k1Point {
            purpose: "scalar_mul",
            ge: (self.ge * *scalar.fe).to_affine(),
        }
    }

    fn generator_mul(scalar: &Self::Scalar) -> Self {
        Secp256k1Point {
            purpose: "generator_mul",
            ge: Secp256k1Point::generator().scalar_mul(scalar).ge,
        }
    }

    fn add_point(&self, other: &Self) -> Self {
        Secp256k1Point {
            purpose: "add_point",
            ge: (ProjectivePoint::from(self.ge) + other.ge).to_affine(),
        }
    }

    fn sub_point(&self, other: &Self) -> Secp256k1Point {
        Secp256k1Point {
            purpose: "sub",
            ge: (ProjectivePoint::from(self.ge) - other.ge).to_affine(),
        }
    }

    fn neg_point(&self) -> Secp256k1Point {
        Secp256k1Point {
            purpose: "neg",
            ge: -self.ge,
        }
    }

    fn scalar_mul_assign(&mut self, scalar: &Self::Scalar) {
        self.purpose = "mul_assign";
        self.ge = (self.ge * *scalar.fe).to_affine()
    }

    fn underlying_ref(&self) -> &Self::Underlying {
        &self.ge
    }
    fn underlying_mut(&mut self) -> &mut Self::Underlying {
        &mut self.ge
    }
    fn from_underlying(ge: Self::Underlying) -> Secp256k1Point {
        Secp256k1Point {
            purpose: "from_underlying",
            ge,
        }
    }
}

impl PartialEq for Secp256k1Point {
    fn eq(&self, other: &Secp256k1Point) -> bool {
        self.underlying_ref() == other.underlying_ref()
    }
}

impl Zeroize for Secp256k1Point {
    fn zeroize(&mut self) {
        self.ge.zeroize()
    }
}

pub mod hash_to_curve {
    use crate::elliptic::curves::wrappers::{Point, Scalar};
    use crate::{arithmetic::traits::*, BigInt};

    use super::Secp256k1;

    /// Takes uniformly distributed bytes and produces secp256k1 point with unknown logarithm
    ///
    /// __Note:__ this function is subject to change
    pub fn generate_random_point(bytes: &[u8]) -> Point<Secp256k1> {
        let compressed_point_len: usize = 33;
        let truncated = if bytes.len() > compressed_point_len - 1 {
            &bytes[0..compressed_point_len - 1]
        } else {
            bytes
        };
        let mut buffer = [0u8; 33];
        buffer[0] = 0x2;
        buffer[1..1 + truncated.len()].copy_from_slice(truncated);
        if let Ok(point) = Point::from_bytes(&buffer) {
            return point;
        }

        let bn = BigInt::from_bytes(bytes);
        let two = BigInt::from(2);
        let bn_times_two = BigInt::mod_mul(&bn, &two, Scalar::<Secp256k1>::group_order());
        let bytes = BigInt::to_bytes(&bn_times_two);
        generate_random_point(&bytes)
    }

    #[cfg(test)]
    mod tests {
        use super::generate_random_point;

        #[test]
        fn generates_point() {
            // Just prove that recursion terminates (for this input..)
            let _ = generate_random_point(&[1u8; 32]);
        }

        #[test]
        fn generates_different_points() {
            let point1 = generate_random_point(&[1u8; 32]);
            let point2 = generate_random_point(&[2u8; 32]);
            assert_ne!(point1, point2)
        }
    }
}

#[cfg(test)]
mod test {
    use sha2::{Digest, Sha256};

    use crate::arithmetic::*;

    use super::{ECPoint, GE};

    #[test]
    fn test_base_point2() {
        /* Show that base_point2() is returning a point of unknown discrete logarithm.
        It is done by using SHA256 repeatedly as a pseudo-random function, with the generator
        as the initial input, until receiving a valid Secp256k1 point. */

        let base_point2 = GE::base_point2();

        let g = GE::generator();
        let hash = Sha256::digest(&g.serialize_compressed());
        let hash = Sha256::digest(&hash);
        let hash = Sha256::digest(&hash);

        assert_eq!(BigInt::from_bytes(&hash), base_point2.x_coord().unwrap());

        // check that base_point2 is indeed on the curve (from_coor() will fail otherwise)
        assert_eq!(
            &GE::from_coords(
                &base_point2.x_coord().unwrap(),
                &base_point2.y_coord().unwrap()
            )
            .unwrap(),
            base_point2
        );
    }
}
