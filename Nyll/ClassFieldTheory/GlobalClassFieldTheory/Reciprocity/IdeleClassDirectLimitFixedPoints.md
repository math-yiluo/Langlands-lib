# Idele class groups as fixed parts of the rational direct limit

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFixedPoints`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite intermediate field `K` of `ℚˢᵉᵖ/ℚ`, the file proves that the part of `rationalIdeleClassRepresentation` fixed by `Gal(ℚˢᵉᵖ/K)` is the idele class group `C_K`. It also proves the Galois naturality of the canonical maps from idele class groups into the direct limit.

## Main definitions

- `rationalIntermediateIdeleClassToFixed K`: the additive homomorphism from `C_K` to `KummerTheory.ambientFixedAddSubgroup rationalIdeleClassRepresentation (closedFixingSubgroup ℚ ℚˢᵉᵖ K)`, the corestriction of `rationalIntermediateIdeleClassToDirectLimit K`.
- `rationalIdeleClassEquivFixed K`: the additive equivalence between `C_K` and that fixed part, obtained from bijectivity.

## Main results

- `rationalRelativeAdeleEmbedding_fixed_of_mem_fixingSubgroup` and `rationalRelativeIdeleClassEmbedding_fixed_of_mem_fixingSubgroup`: the scalar extension from `K` to a finite Galois level `N` of a relative adele, or of a relative idele class, is fixed by every `σ` fixing `K`.
- `rationalIntermediateIdeleClassToDirectLimit_conjugation`: if `σ` restricts on `E` to `τ ∈ Aut(E/ℚ)`, acting by `σ` on the image of a class `c` gives the image of `τ • c`.
- `rationalIntermediateIdeleClassToDirectLimit_ambientAlgEquiv`: if `e : E ≃ F` is induced by `σ`, then `σ` sends the image of `c ∈ C_E` to the image of `ideleClassCongr e c ∈ C_F`.
- `rationalIntermediateIdeleClassToDirectLimit_fixed` and `rationalIntermediateIdeleClassToDirectLimit_mem_fixed`: the image of `C_K` is fixed by `Gal(ℚˢᵉᵖ/K)`.
- `rationalIntermediateIdeleClassToFixed_injective` and `rationalIntermediateIdeleClassToFixed_surjective`.

## Proofs

The naturality statements are checked at the normal closure, or at the compositum of two normal closures, where the action is restriction of `σ`. Injectivity combines injectivity of the level map into the limit with injectivity of scalar extension; surjectivity is the descent theorem `rationalDirectLimit_fixed_exists_ideleClass`.

## Points to watch

- `K` must be finite over `ℚ`; the fixed part is taken under the closed fixing subgroup of `K`.
- `rationalIdeleClassEquivFixed` is built with `AddEquiv.ofBijective`, so its inverse is not given by a formula.
- The homomorphism and the equivalence to the fixed part (and `rationalIntermediateIdeleClassToDirectLimit_mem_fixed`) use the additive form `Additive (IdeleClassGroup K)`; the scalar-extension, naturality and `rationalIntermediateIdeleClassToDirectLimit_fixed` statements are multiplicative.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/IdeleClassDirectLimitFixedPoints.lean`: the Lean file is the source byte for byte (SHA-256 `af6f2fe1601c7e0c714c1308acfe4e97df8e381b298f65fd84fbb877bbc1521e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
