# Finite extensions and norms to ℚ in the rational idele-class representation

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitExtension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a pair of closed subgroups `L ≤ K` of `Gal(ℚˢᵉᵖ/ℚ)`, the file identifies the fixed representation of the abstract extension with the relative idele class group of the actual fixed fields `F ⊆ E`. It also shows that the class-formation norm down to `ℚ` is the ordinary idele-class norm.

## Main definitions

- `rationalAbstractExtensionIdeleClassEquiv K L hLK hnormal`: assume `L` is normal in `K` (normality of `extensionSubgroup K L hLK`), `K` has finite index in the whole group and `L` finite index in `K`. With `F` the fixed field of `K` and `E` the relative fixed field of `L`, the module of `extensionFixedRepresentation rationalIdeleClassRepresentation K L hLK hnormal` is additively equivalent to `RelativeIdeleGroup.ClassGroup F E`. It composes the fixed-part comparison, the base change to `IdeleClassGroup E` and the tower comparison.

## Main results

- `rationalIdeleClassEquivFixed_relativeCosetAction_coe`: for a finite intermediate field `K`, the action of a left coset `q` of `Gal(ℚˢᵉᵖ/K)` on the image of a class `c` is the class embedding of `c` along the embedding of `K` into its normal closure that `rationalBaseFixingCosetEquivNormalClosure` attaches to `q`.
- `rationalIdeleClassEquivFixed_relativeNorm_coe`: the class-formation `relativeNorm` from `Gal(ℚˢᵉᵖ/K)` to the whole group, applied to the image of `c`, is the relative idele-class norm of `c` from `K` to `ℚ` (`RelativeIdeleGroup.Cohomology.ideleClassNorm ℚ K c`), placed diagonally at the normal closure of `K` and mapped into the direct limit.
- `rationalAbstractFixedFieldIdeleClassEquivFixed_normToBase_coe`: the same for `normToBase` and a finite-index closed subgroup `H` with its fixed field.
- `rationalAbstractFixedFieldNormToBase_eq_ordinaryIdeleClassNorm`: for a finite abstract field `H` with fixed field `F`, pulling `normToBase` back through `rationalIdeleClassEquivBaseFixed` gives the ordinary norm `ideleClassNorm ℚ F : C_F → C_ℚ`.

## Proofs

The norm is a sum over cosets; the coset action lemma turns it into the product over the embeddings of `K` into its normal closure, which is the norm by an imported product formula. The closed-subgroup versions transport along the identification of a subgroup with the fixing group of its fixed field.

## Points to watch

- Normality of `L` in `K` and both finiteness conditions are explicit hypotheses of the equivalence.
- The norm comparisons in this file go only down to `ℚ`. The two norm formulas ending in `_coe` are equalities of underlying direct-limit elements, whose right-hand side is the image under `rationalRelativeIdeleClassToDirectLimit` of a diagonal class at a normal closure, not an element of `C_ℚ`; only the last theorem lands in the idele class group of `ℚ`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/IdeleClassDirectLimitExtension.lean`: the Lean file is the source byte for byte (SHA-256 `bf7cb9d914ae4159386c247c1352bc62e0862f033040fb5ad4dba76f63ecfbd5`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
