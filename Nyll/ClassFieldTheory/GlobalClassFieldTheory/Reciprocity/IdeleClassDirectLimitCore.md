# The rational idele-class direct limit

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitCore`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file builds the coefficient module of the global class formation over `ℚ`: the direct limit, over the finite Galois subextensions `E` of `ℚˢᵉᵖ/ℚ`, of the relative idele class groups `RelativeIdeleGroup.ClassGroup ℚ E` (the library's presentation of the idele class group of `E` through relative adeles over `ℚ`), with the action of `Gal(ℚˢᵉᵖ/ℚ)`.

## Main definitions

- `rationalAbsoluteGaloisIdeleClassAction E` and the instance `rationalFiniteGaloisIdeleClassMulDistribMulAction`: `σ ∈ Gal(ℚˢᵉᵖ/ℚ)` acts on the level `E` through its restriction to `E`.
- `rationalRelativeIdeleClassTransition h`: for `E ≤ F`, the scalar-extension map between levels, as an equivariant homomorphism; the instance `rationalRelativeIdeleClassDirectedSystem` makes these a directed system.
- `rationalIdeleClassDirectLimit`: Mathlib's `DirectLimit` of this system; `rationalRelativeIdeleClassToDirectLimit E` is the canonical homomorphism from level `E`.
- `rationalIdeleClassDirectLimitMulDistribMulAction` and `rationalIdeleClassDirectLimitSMul`: the induced Galois action, supplied by Mathlib.
- `rationalIdeleClassRepresentation`: the resulting `Rep ℤ` of `Gal(ℚˢᵉᵖ/ℚ)`.

## Main results

- Equivariance of scalar extension: along `E ≤ F` with `F` finite Galois, extension of relative adeles, ideles and idele classes turns the action of `τ ∈ Aut(E/ℚ)` into that of any `σ` extending `τ` (the `..._conjugation_of_restrict` lemmas); `rationalRelativeIdeleClassEmbedding_smul` is the case of two finite Galois levels.
- `rationalRelativeIdeleClassEmbedding_smul_eq_classEmbedding`: acting by `σ` after extension is extension along the embedding `σ|_F ∘ (E ↪ F)`.
- Identity and transitivity of scalar extension (`_self`, `_comp` lemmas), and `rationalIdeleClassDirectLimit_mk_apply`, the defining relation of the limit.
- `rationalRelativeIdeleClassEmbedding_classInclusion`: extension sends the diagonal class of a rational idele class to the diagonal class.

## Points to watch

- The direct limit is the library's own model of the idele class group of `ℚˢᵉᵖ`. It runs over finite Galois subextensions only, and its levels are relative idele class groups, not `IdeleClassGroup E`.
- Injectivity of the transition maps and the identification of fixed parts are not proved here, and no continuity property of the action is stated.
- The file declares global instances, among them an `Algebra ℚ (SeparableClosure ℚ)` taken from the realization of the separable closure inside `AlgebraicClosure ℚ`, an algebra structure on rational intermediate fields from their inclusion, and `NumberField` for finite-dimensional ones.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/IdeleClassDirectLimitCore.lean`: the Lean file is the source byte for byte (SHA-256 `46a1be929ae49ad2f964805509dfdb4e614f3cad12fde480659b188fdf9107da`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
