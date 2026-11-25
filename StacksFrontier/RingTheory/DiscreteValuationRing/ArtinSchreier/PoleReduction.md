# Minimal pole order, residue lifts and Laurent expansions for Artin–Schreier presentations

Module `StacksFrontier.RingTheory.DiscreteValuationRing.ArtinSchreier.PoleReduction`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file treats Artin–Schreier presentations z^p − z = ξ of an extension M/L, where L is the fraction field of a discrete valuation ring B with uniformizer π. The pole order of ξ, the least n with π^n ξ in B, is expressed through membership in the image of B, not by a definition. The file chooses a presentation of minimal pole order and provides residue lifts and Laurent expansions.

## Main results

- `exists_artinSchreier_presentation_minimal_poleOrder`: if M = L[z] for some z with z^p − z in L, some such presentation has minimal pole order among all of them.
- `adjoin_singleton_sub_algebraMap`: translating a generator by an element of the base ring does not change the subalgebra it generates.
- `exists_residueField_lift_mod_pow`: a discrete valuation ring of characteristic p and N > 0 admit a set-theoretic section of the residue map whose reduction modulo m^N is a ring homomorphism.
- `exists_sub_algebraMap_mem_pow_of_pow_eq_over_residueField`: let A → B be a local homomorphism of local rings, B of characteristic p, F a field with a ring map to κ(B), and σ lifts from F to B whose reduction modulo m_B^N is a ring homomorphism. If a in F has a p^N-th root x whose image in κ(B) comes from κ(A), then σ(a) agrees modulo m_B^N with an element of A. No section of the whole residue field of B is needed.
- `exists_laurent_expansion`: for a section σ of the residue map of B, if π^n ξ lies in B, then ξ is b in B plus the sum of σ(cᵢ) π^(−(n−i)) over i < n.

Private lemmas give the congruence α^|V| ≡ π modulo π^N when ∏ (α − v) over v in V equals π and V ⊆ π^N A, and expand an element of B in powers of π with lifted residue coefficients.

## Points to watch

- `exists_residueField_lift_mod_pow` gives a section compatible modulo m^N only, not a coefficient field.
- The pole-reduction step by a translation and the constant-numerator obstruction that the module docstring announces are not in the file.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/ArtinSchreier/PoleReduction.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 21 declarations of the source file 11 are kept. The 10 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.artinSchreier_sub_poleReduction`, `IsDiscreteValuationRing.artinSchreier_sub_poleReduction_eq`, `IsDiscreteValuationRing.exists_eq_pow_add_uniformizer_mul`, `IsDiscreteValuationRing.exists_eq_pow_add_uniformizer_mul_of_root`, `IsDiscreteValuationRing.exists_sub_algebraMap_mem_pow_of_perfect_residueField`, `IsDiscreteValuationRing.exists_sub_algebraMap_mem_pow_of_pow_eq`, `IsDiscreteValuationRing.not_dvd_poleOrder_of_constant_numerator`, `IsDiscreteValuationRing.not_dvd_poleOrder_of_constant_numerator_of_root`, `IsDiscreteValuationRing.not_minimal_poleOrder_of_pow_add`, `IsDiscreteValuationRing.perfectRing_of_range_eq_iInf_pow`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
