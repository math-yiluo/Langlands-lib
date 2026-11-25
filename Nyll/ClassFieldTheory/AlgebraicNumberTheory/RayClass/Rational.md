# Ray class groups of ℚ are (ℤ/m)ˣ

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Rational`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a positive integer m, the ray class group of ℚ for the modulus with finite part (m) and the real place is isomorphic to (ℤ/mℤ)ˣ, in both its ideal and its idelic form. The isomorphism sends an ideal prime to m to the residue of its positive generator.

## Definitions

- `rationalFiniteModulus m`: the finite modulus with exponent `m.factorization p` at the prime over p. `rationalModulus m` is `Modulus.narrowOfFinite` of it, so it also imposes positivity at the real place.
- `positiveRationalIdealGenerator I`: the positive generator of a nonzero fractional ideal of ℚ, multiplicative in I. A local instance makes 𝓞 ℚ a principal ideal ring. `positiveRationalIdealGeneratorUnit` is its version in ℚˣ.
- `rationalResidueUnit m q`: for q whose numerator and denominator are prime to m, the unit num(q)·den(q)⁻¹ of `ZMod m`. It is multiplicative, and `rationalResidueUnit_eq_one_iff_modEq` says it equals 1 if and only if num(q) ≡ den(q) mod m.
- `primeToIdealResidueHom m hm`: the homomorphism from the ideals prime to `rationalModulus m` to `(ZMod m)ˣ` that sends I to the residue of its positive generator.

## Main results

- `principalLocalHigherUnit_iff_modEq`: let x ∈ ℚˣ have valuation 1 at the prime v over p. The v-component of its principal idele lies in `localHigherUnitGroup v n` if and only if num(x) ≡ den(x) mod pⁿ.
- `principalIdele_infinite_mem_iff_pos`: the infinite component of the principal idele of x lies in `narrowInfiniteCongruenceSubgroup` if and only if x > 0.
- `mem_principalRayIdealSubgroup_iff_modEq`: an ideal I prime to m is ray-principal if and only if its positive generator q satisfies num(q) ≡ den(q) mod m.
- `primeToIdealResidueHom_surjective` and `primeToIdealResidueHom_ker`: the residue map is onto, and its kernel is `principalRayIdealSubgroup (rationalModulus m)`.
- `idealRayClassGroupEquivZModUnits m hm`: `IdealRayClassGroup (rationalModulus m) ≃* (ZMod m)ˣ`.
- `rationalRayClassGroupEquivZModUnits m hm`: the same for the idelic `RayClassGroup (rationalModulus m)`, through the imported `rayClassGroupEquivIdealRayClassGroup`.

## Proof

The local criterion passes to the p-adic integers by `padicIntEquiv`, where the n-th power of the maximal ideal is the kernel of `PadicInt.toZModPow n`. For the kernel, positivity at the real place forces a ray generator to be the positive generator. The congruences at the primes dividing m combine into one mod m by a Chinese remainder argument, `intModEq_of_primePower_modEq`. A unit u is the image of the principal ideal of val(u) + m.

## Points to watch

- All equivalences assume m ≠ 0.
- The modulus always contains the real place. The modulus with finite part (m) and no infinite place is not treated.
- The isomorphism goes from ideals to residues. It is not stated in terms of Frobenius elements or the Artin map.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/RayClass/Rational.lean`: the Lean file is the source byte for byte (SHA-256 `3a1d341fb130cc8b9efdc3a4349d292db1197cfd83ec80049da4f2bc6b319776`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
