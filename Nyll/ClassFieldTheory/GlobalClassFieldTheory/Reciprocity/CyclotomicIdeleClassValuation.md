# The cyclotomic valuation on idele class groups

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicIdeleClassValuation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The cyclotomic ℤ̂-valued idele value is trivial on principal ideles, so it descends to the idele class group. This file builds the descended value over ℚ (v_ℚ) and the normalized one over a number field K (v_K), proves both surjective, computes the image of the idele-class norm under v_ℚ, and packages the result as the concrete valuation datum of abstract class field theory over ℚ.

## Main definitions and results

- `ideleClassContinuousQuotientLift`: a continuous homomorphism that kills a normal subgroup descends continuously to the quotient.
- `rationalCyclotomicZHatIdeleClassValueContinuous` (v_ℚ on C_ℚ) and `normalizedCyclotomicZHatIdeleClassValueContinuous K` (v_K on C_K), each with a multiplicative `...Mul` form and simp lemmas on representatives.
- `infiniteGlobalArtinMonoidHom_numberFieldCyclotomicZHatCompositum_principalIdele`: the library's infinite Artin map of K·T/K, with T the cyclotomic ℤ̂-extension of ℚ, kills principal ideles. It descends to `numberFieldCyclotomicZHatCompositumIdeleClassArtinMonoidHom`. In the ℤ̂ coordinate of Gal(T/ℚ), its restriction to T is f_K · v_K(c) (`..._coordinate`), and its kernel is the zero fibre of v_K (`..._eq_one_iff`). Here f_K is `cyclotomicZHatIntersectionDegree K`.
- The same descent for each finite Galois layer E of T/ℚ (`numberFieldCyclotomicZHatFiniteLayerIdeleClassArtinMonoidHom`), compatible with restriction from the full compositum.
- `rationalCyclotomicZHatIdeleClassValue_surjective`, `normalizedCyclotomicZHatIdeleClassValue_surjective`: both values are surjective, already on norm-one idele classes, so their ranges are all of ℤ̂.
- `cyclotomicZHatIntersectionDegree_nsmul_normalizedIdeleClassValue`: f_K · v_K(c) = v_ℚ(N c), where N is the idele-class norm from K to ℚ.
- `rationalCyclotomicZHatIdeleClassNormComposite_range`: the image of v_ℚ ∘ N on C_K is f_K · ℤ̂, already attained on norm-one classes.
- `rationalCyclotomicZHatValuation`: v_ℚ moved to the base-fixed part of `rationalIdeleClassRepresentation`; it is surjective. For the number field F fixed by a finite abstract field `H`, the image under this valuation of the norm to the base is the residue degree of `H` times ℤ̂ (`rationalCyclotomicZHatValuation_normToBase_range`).
- `rationalCyclotomicIdeleClassValuationData`: the `ValuationData` for `rationalCyclotomicDegreeData` built from these facts. `rationalCyclotomicIdeleClassValuationData_valuationAt_fixed_apply` (simp): its valuation at `H`, read on C_F, is v_F.

## Proofs

Surjectivity comes from an imported density statement on norm-one ideles: the image of the compact norm-one idele class group is dense and compact, hence everything. The vanishing of the Artin map on principal ideles is checked after the injective restriction to T, using norm functoriality and the imported rational principal-idele formula. The range statements combine the identity f_K · v_K = v_ℚ ∘ N with surjectivity of v_K; for abstract fixed fields they also use that the intersection degree equals the residue degree (`cyclotomicZHatIntersectionDegree_abstractFixedField_eq_residueDegree`).

## Watch for

- `ValuationData`, `FiniteAbstractField` and the residue degree are the library's own notions of abstract class field theory.
- The Artin maps are the library's own, built from chosen local factors.
- The results for a general number field take `K : Type`, in universe 0.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/CyclotomicIdeleClassValuation.lean`: the Lean file is the source byte for byte (SHA-256 `2d0f00fddd879bdc8285e63cb15f85f6ca676a4417dc5a0e102bfd1e4a732043`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
