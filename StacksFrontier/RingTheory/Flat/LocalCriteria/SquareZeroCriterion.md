# Comparison of fibres and the first steps of the local flatness criterion

Module `StacksFrontier.RingTheory.Flat.LocalCriteria.SquareZeroCriterion`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file compares fibres computed over a ring and over an algebra, provides the canonical local homomorphism from R localized at p to S localized at q, and proves the first auxiliary steps of the local flatness criterion of Tag 00ME.

## Main results

- `isBaseChange_mkQ_smul_top`: for an ideal K of R, the quotient map M → M/KM exhibits M/KM as the base change of M along R → R/K.
- `Module.Flat.mem_map_smul_top_iff`: for an R-algebra S and a module with compatible actions, the S-submodule (IS)M and the R-submodule IM have the same elements.
- `TensorProduct.exists_one_tmul` and `TensorProduct.one_tmul_eq_zero_iff_mem_smul_top`: every element of (A/J) ⊗_A X is some 1 ⊗ y, and 1 ⊗ y vanishes exactly when y ∈ JX.
- For a prime q of an R-algebra S with contraction p, `Ideal.algebraLocalizationAtPrimeUnder` gives the canonical local map from Rₚ to S localized at q as an algebra structure, with its scalar tower (`Ideal.isScalarTower_localizationAtPrimeUnder`) and its locality (`Ideal.isLocalHom_algebraMap_localizationAtPrimeUnder`). For any Rₚ-algebra structure on that localization compatible with R, `Ideal.map_maximalIdeal_eq_map_under` identifies the extensions of the maximal ideal of Rₚ and of p.

The private lemmas of `Stacks.Flatness.LocalCriterion` are the residue-field argument behind Tag 00ME. For a maximal ideal 𝔪, M flat and u : N → M with R/𝔪 ⊗ u injective, they split R/𝔪 ⊗ u over the field R/𝔪 and propagate the inclusion u⁻¹(JM) ⊆ JN through the filtration by 𝔪ⁿ + I (`comap_smul_top_pow_add_le`). A separate lemma, `flat_quotient_range_of_comap_smul_top_le`, gives flatness of the cokernel M/u(N) when u⁻¹(IM) ⊆ IN for every ideal I.

The file has two module docstrings. The first announces the square-zero case of the local criterion and Tag 051I, which are not in the file. The second, headed "Criteria for flatness over a Noetherian local base", lists results for Tags 00ME to 0H7N, none of which is stated here; 00ME itself is stated in `StacksFrontier.RingTheory.Flat.LocalCriteria.FibreCriteria`.

## References

Tag 00ME. The base-change description of M/KM cites EGA 0 22.4.5 and SGA 7 VIII 2.1.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 22.4.5 | `isBaseChange_mkQ_smul_top` | partial |
| SGA | 7 VIII 2.1 | `isBaseChange_mkQ_smul_top` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/LocalCriteria/SquareZeroCriterion.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 33 declarations of the source file 23 are kept. The 10 left out are not needed by the results for which the extract is made: `Ideal.eq_of_le_sup_map_of_flat_quotient`, `Ideal.inf_map_eq_smul_of_flat_quotient`, `flat_of_sq_zero_local_criterion`, `flat_quot_idealTwo_smul_top_of_flat_quot_and_flat_baseChange`, `hquot_from_h1`, `htor_core_rTensor_inj`, `htor_from_base_change`, `htor_rTensor_subtype_injective`, `killed_of_sq_bot`, `rTensor_subtype_baseChange_inj`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
