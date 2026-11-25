# Adjoining the fourth roots of unity to a number field

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.ComplexificationArtin.NumberFieldComplexification`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `F`, the file forms the compositum `F(μ₄)` of a fixed copy of `F` with the field of fourth roots of unity, inside `SeparableClosure ℚ`, and shows that restriction of `Gal(F(μ₄)/F)` to the rational fourth-root field is injective, so that `F(μ₄)/F` is abelian.

## Main definitions and results

- `rationalComplexificationAmbientField`: the rational fourth-root cyclotomic field `rationalComplexificationCyclotomicField` lifted into `SeparableClosure ℚ`, with `rationalComplexificationAmbientEquiv` identifying the two.
- `numberFieldComplexification F`: the compositum of `numberFieldInRationalSeparableClosure F`, the copy of `F` given by the standard embedding `numberFieldSeparableClosureEmbedding F`, with that field. Instances make it a number field and an algebra over `F` (through `numberFieldComplexificationEmbedding F`) and over the cyclotomic field, with scalar towers over `ℚ` and finite dimension over `F`.
- `numberFieldComplexificationRestriction F : Gal(F(μ₄)/F) →* Gal(ℚ(μ₄)/ℚ)`: restriction to the cyclotomic factor.
- `numberFieldComplexificationRestriction_injective`: this restriction is injective.
- `numberFieldComplexification_isAbelianGalois`: `F(μ₄)/F` is abelian Galois.

## Proof

Inside `F(μ₄)` the copy of `F` and the cyclotomic layer generate everything; restriction of automorphisms over `F` to the cyclotomic layer is then injective by the corresponding Mathlib result for a compositum. Galois-ness over `F` comes from `IsGalois.sup_right`, and commutativity from the injective restriction into the abelian group `Gal(ℚ(μ₄)/ℚ)`.

## Caveats

- The compositum is taken in `SeparableClosure ℚ` with the library's standard embedding of `F`, not inside `ℂ`; the field `L(i)` built at an infinite place elsewhere is a different construction inside `ℂ`.
- The algebra and scalar-action structures of `F` and of the cyclotomic field on `F(μ₄)` are declared as global instances through the chosen embeddings.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/ComplexificationArtin/NumberFieldComplexification.lean`: the Lean file is the source byte for byte (SHA-256 `71fd13fb887278ec2ea52a487a3694553637c9a0095751456fba5da236851f10`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
