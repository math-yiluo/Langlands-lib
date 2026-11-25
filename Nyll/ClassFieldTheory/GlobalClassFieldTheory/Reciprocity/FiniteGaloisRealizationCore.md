# Realizing a finite Galois tower L/K inside the separable closure of ℚ

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteGaloisRealizationCore`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

To apply the rational class formation to a finite Galois extension L/K of number fields, the tower must sit inside ℚ̄ = `SeparableClosure ℚ` by compatible embeddings. The file uses the library's one chosen embedding of L (`numberFieldSeparableClosureEmbedding L`) and takes for K its restriction along K → L. It then sets up the field ranges, their fixing subgroups, and the absolute Galois group of K realized on ℚ̄.

## Main definitions and results

- `numberFieldTowerLowerEmbedding K L : K →ₐ[ℚ] ℚ̄`, the restricted embedding, and `numberFieldTowerBaseField K L`, its image. The image lies in the image of L (`numberFieldTowerBaseField_le_topField`). Instances make it a number field, the image of L finite-dimensional and Galois over it, and the square with L/K commute (`numberFieldTowerFieldRangeEquiv_algebraMap`).
- `numberFieldTowerBaseSubgroup K L` and `numberFieldTowerTopSubgroup L`: the closed fixing subgroups of the two images in Gal(ℚ̄/ℚ), with top ≤ base.
- `numberFieldTowerSeparableClosureBaseAlgebra`, `...TopAlgebra`: the K- and L-algebra structures on ℚ̄ given by the two embeddings. With them ℚ̄ is a scalar tower over ℚ → K → L. It is Galois over K and over L, through Mathlib's `IsSepClosure.equiv`; `numberFieldTowerSeparableClosureEquiv` identifies `SeparableClosure K` with ℚ̄ over K.
- `numberFieldTowerSeparableClosureRestriction K L : Gal(ℚ̄/K) →ₜ* Gal(L/K)`: continuous restriction. It equals `AlgEquiv.restrictNormalHom L` (simp) and is surjective.
- `numberFieldTowerSeparableClosureEquivBaseSubgroup K L : Gal(ℚ̄/K) ≃* numberFieldTowerBaseSubgroup K L`: a K-automorphism of ℚ̄, viewed as a ℚ-automorphism, fixes the image of K, and conversely. Its coercion is restriction of scalars (simp).
- A scalar-tower statement for the compositum Lℚ̃ of L with the cyclotomic ZHat-extension, inside ℚ̄.

## Proof

Continuity of restriction is reduced to Mathlib's continuity of restriction to the field range of L, composed with an isomorphism of finite discrete groups.

## Points to watch

- All of this depends on the chosen embedding of L; K is embedded through L, not through its own chosen embedding `numberFieldSeparableClosureEmbedding K`. The two copies of K in ℚ̄ need not coincide.
- The K-algebra structure on ℚ̄ is a non-instance definition, supplied by `let` in each statement. Statements about `Gal(SeparableClosure ℚ / K)` refer to that structure.
- The module heading mentions norm comparison. This file contains only the field-theoretic and Galois-group setup; no idele class group or norm quotient appears in it.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/FiniteGaloisRealizationCore.lean`: the Lean file is the source byte for byte (SHA-256 `795d4a8abb35fba2177458f5e61172b0cb0a3a5644a85d0df4d1aeef50994458`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
