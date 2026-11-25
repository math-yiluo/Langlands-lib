# Decomposition groups and p-adic coordinates of the cyclotomic ℤ̂-extension

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceCyclotomicFrobeniusLift`, copied from the Lean library NYLL with one local instance replaced (see "Changed declarations"). The origin of the file is given at the end of this page.

The file collects ingredients for lifting Frobenius elements inside a prescribed decomposition group, for the local–global compatibility theorem. It works with the library's cyclotomic ℤ̂-extension ℚ̃ = `rationalCyclotomicZHatField` of ℚ (Galois group ℤ̂) and its compositum Fℚ̃ with a number field F.

## Main definitions and results

- `absoluteValueDecompositionGroupRestrictionHom`: for K ⊆ L ⊆ Ω with L/K normal, restriction from the decomposition group of an absolute value on Ω to that of its restriction to L; surjective when Ω/K is Galois and the absolute value extends a nontrivial one of K (`absoluteValueDecompositionGroupRestrictionHom_surjective`).
- `infiniteGlobalArtinMonoidHom_finitePlaceIdele_mem_absoluteValueDecompositionGroup`: for an abelian, possibly infinite, extension A/F and an extension w of the v-adic absolute value to A, the Artin symbol of an idele supported at v lies in the decomposition group of w.
- For a finite Galois layer E of ℚ̃, restriction Gal(FE/F) → Gal(E/ℚ) is injective with image the fixing subgroup of F ∩ E. For ℚ̃ itself, the coordinate `numberFieldCyclotomicZHatCompositumCoordinate F` : Gal(Fℚ̃/F) → ℤ̂ is injective with image f_F·ℤ̂, f_F = `cyclotomicZHatIntersectionDegree F`; so Gal(Fℚ̃/F) is torsion-free.
- `exists_positiveZHatDegree_lift_of_surjective`: if D → A is surjective and a degree map D → ℤ̂ sends the kernel to a finite-index subgroup, every element of A lifts to one of positive integer degree. `MonoidHom.ext_of_eq_on_finitePrimaryComponents`: homomorphisms from a finite commutative group to a commutative group are determined on primary components.
- `numberFieldCyclotomicPadicDecompositionCoordinate F wC p`: the ℤ_p-coordinate (`rationalCyclotomicPadicCoordinate p`) on the decomposition group of an absolute value wC of Fℚ̃. Its image is closed, and nonzero and of finite index in ℤ_p when wC extends the v-adic absolute value of a finite place v (`..._range_toAddSubgroup_ne_bot`, `..._range_index_ne_zero`); the variants `_of_isEquiv` and `_of_base_isEquiv` relax this to equivalence of absolute values.
- `rationalCyclotomicPadicFieldWithinZHat p` (Galois group ℤ_p), its copy `rationalCyclotomicPadicField p` in the separable closure, and finite layers `rationalCyclotomicPadicFiniteLevel p n` with Galois group `ZMod (p^n)` and degree p^n (`rationalCyclotomicPadicFiniteLevel_finrank`). Over F, the compositum with such a layer has cyclic Galois group (`numberFieldCyclotomicPadicFiniteCompositum_isCyclic`).

## Proof of the finite-index statement

The witness is a one-place idele at v whose component extends the rational number p + 1 (if v lies over p) or the residue prime q (otherwise); its norm is a positive power of a rational one-place idele. The cyclotomic character formulas (the unit p + 1, resp. q⁻¹) show the value is not torsion, so the coordinate is nonzero. A closed nonzero subgroup of ℤ_p is open, hence of finite index.

## Points to watch

- Despite its heading, the file constructs no Frobenius lift; it supplies the inputs for one.
- ℚ̃ is the ℤ̂-extension, not ℚ(μ_∞); the "p-primary" field is the ℤ_p-extension in ℚ̃.

## Changed declarations

The source declares the anonymous local instance `local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩` in namespace `GlobalClassFieldTheory.Reciprocity`. Lean names it from its type, and other modules of the copy declare the same name, so the modules could not be imported together. Here the declaration is replaced by `attribute [local instance] fact_prime_val`, where `GlobalClassFieldTheory.Reciprocity.fact_prime_val : ∀ (p : Nat.Primes), Fact p.1.Prime` (proof `⟨p.2⟩`, module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PrimesFact`, imported with `public import`) has the same type and proof. The instance stays local to the file; no statement or proof of the file changes otherwise.

## Origin of the file

Copied from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/FinitePlaceCyclotomicFrobeniusLift.lean`. The Lean file is the source byte for byte except for the change above (SHA-256 of the source: `54ed71ddccf2cd5977a1409f71d0bbe86bcd7e4c323fce2c58682ac06d3d5759`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
