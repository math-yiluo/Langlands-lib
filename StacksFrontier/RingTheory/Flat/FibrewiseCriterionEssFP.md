# Fibrewise flatness for essentially finitely presented algebras

Module `StacksFrontier.RingTheory.Flat.FibrewiseCriterionEssFP`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a local tower R → S → S′, this file uses the closed fibre of an S′-module to test its flatness over S and the flatness of S over R.

`Module.flat_algebra_and_flat_of_flat_quotient_maximalIdeal` assumes local homomorphisms of local rings and essential finite presentation of R → S and R → S′. Let M be a nonzero finitely presented S′-module, flat over R, with the compatible actions from the tower. If M/𝔪M is flat over S/𝔪S for the maximal ideal 𝔪 of R, then S is flat over R and M is flat over S.

For a compatible tower R → A → S → C with S a localization of A, `Stacks.Flatness.EssFPFibrewiseCriterion.tmul_one_sub_one_tmul_mem_of_isLocalization` says that an ideal of S ⊗ᵣ C containing the differences a ⊗ 1 − 1 ⊗ a for a set of R-algebra generators of A contains the corresponding difference for every x in S.

The proof uses these differences to generate the kernel of S ⊗ᵣ S′ → S′ from finitely many relations. Clearing denominators presents S′ as a localization of a finitely presented S-algebra. The local flatness criterion then applies over S because R-flatness of M makes the tensor of 𝔪S ↪ S with M over S injective. Nakayama's lemma yields faithful flatness over S, which descends R-flatness from M to S.

Essential finite presentation uses the library predicate `RingHom.EssentiallyOfFinitePresentation`, given by localization of a finitely presented algebra. The fibre quotient is formed over S by (𝔪S)M, giving it the S/𝔪S-action.

The criterion is Tag 00R7, with the finiteness notion from Tag 00QM. The change of base for essential finite presentation is part of EGA IV 1.3.10. The criterion is a special case of EGA IV 11.3.10 and gives the implication (ii) ⇒ (i) from SGA 1 IV 5.9 in this setting. Further correspondences appear in the table of references below.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00R7](https://stacks.math.columbia.edu/tag/00R7) | `Module.flat_algebra_and_flat_of_flat_quotient_maximalIdeal` | Hypothesis (1) is `RingHom.EssentiallyOfFinitePresentation` (Definition 00QM (2)) applied to `algebraMap R S` and `algebraMap R S'`, Mathlib having no such predicate. The fibre is `M ⧸ (𝔪S) • (⊤ : Submodule S M)` over the ring `S ⧸ 𝔪S`, as in 06A5, and the two conclusions are conjoined; see the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 1.3.10 | `essentiallyOfFinitePresentation_of_tower` | partial |
| EGA | IV 11.3.10 | `Module.flat_algebra_and_flat_of_flat_quotient_maximalIdeal` | special case |
| SGA | 1 I 5.9 | `Module.flat_algebra_and_flat_of_flat_quotient_maximalIdeal` | partial |
| SGA | 1 IV 5.9 | `Module.flat_algebra_and_flat_of_flat_quotient_maximalIdeal` | (ii) ⇒ (i) |
| SGA | 3 VIB 1.3.0 | `Module.flat_algebra_and_flat_of_flat_quotient_maximalIdeal` | special case |
| SGA | 3 VIB 12.7 | `Module.flat_algebra_and_flat_of_flat_quotient_maximalIdeal` | special case |
| SGA | 3 VIB 2.5 | `Module.flat_algebra_and_flat_of_flat_quotient_maximalIdeal` | flatness clause |
| SGA | 3 X 3.5 | `Module.flat_algebra_and_flat_of_flat_quotient_maximalIdeal` | Flat case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/FibrewiseCriterionEssFP.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 8 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
