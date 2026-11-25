# Tensor injectivity for modules killed by an ideal

Module `StacksFrontier.RingTheory.Flat.LocalCriteria.SquareZeroTor`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file supplies tensor arguments for the local flatness criterion along an ideal J of a commutative ring S, for an S-module N with N/JN flat over S/J.

## Injectivity after tensoring

- `factB_Jkilled` shows that tensoring with N preserves injections between S-modules annihilated by J. It takes both modules in one universe; its private core `factB_Jkilled_aux` does not. `step2_Jkilled_lTensor_subtype` gives this for the inclusion of a submodule into a module annihilated by J.
- Assume additionally that multiplication J ⊗ₛ N → N is injective. For Q annihilated by J, `tor_vanishing_Jkilled_first_slot` gives the injectivity expressing Tor₁(Q, N) = 0 over S. It combines `tor_smul_top_free_rTensor_inj`, which uses only the multiplication hypothesis, with `tor_first_slot_ladder`, a comparison of free presentations through the chase `ladder_chase`.
- Over any commutative ring, for a short exact sequence 0 → M → L → P → 0, `lemmaC_reduction_tor` preserves injectivity of M → L after tensoring with A, given `hTor`, the injectivity expressing Tor₁(A, P) = 0. It is Mathlib's `LinearMap.lTensor_injective_of_exact_of_flat` with flatness of P weakened to that injectivity; `lemmaC_aux_inj_of_exact_zero` reads exactness of 0 → X → Y as injectivity.

The proof compares the free presentations of Q over S and S/J. The first uses injectivity of multiplication on each direct summand, and the reduced presentation uses flatness over S/J. A snake-lemma argument gives the criterion for tensoring short exact sequences.

The Tor statements are expressed as injectivity after tensoring the kernel inclusion from a canonical free presentation. No result of the file assumes J² = 0. Its second module docstring states the flatness of M/I₂M over R/I₂ after a change of rings, for I₂ the contraction of I²R′; that result is not in the file.

## References

SGA 1 IV 5.2 ((ii) ⇒ (i)) and 5.3 are cited for the special cases of Tor vanishing. SGA 3 VIB 11.7 and 12.7 are cited for the affine tensor comparisons and the Tor reduction.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 3 VIB 11.7 | `step2_Jkilled_lTensor_subtype` | affine case |
| SGA | 3 VIB 12.7 | `lemmaC_reduction_tor` | Vanishing of Tor₁^A(M |
| SGA | 3 VIB 12.7 | `tor_first_slot_ladder` | partial |
| SGA | 1 IV 5.2 | `tor_vanishing_Jkilled_first_slot` | (ii) ⇒ (i), special case |
| SGA | 1 IV 5.3 | `tor_vanishing_Jkilled_first_slot` | special case |
| SGA | 3 VIB 12.7 | `tor_vanishing_Jkilled_first_slot` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/LocalCriteria/SquareZeroTor.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 19 declarations of the source file 11 are kept. The 8 left out are not needed by the results for which the extract is made: `factB_Jkilled'`, `idealTwo`, `image_I_sq_eq_bot`, `lemmaC_smul_top_subtype_lTensor_injective`, `lemmaC_tor_vanishing_Jkilled`, `smul_top_quotient_eq_bot_of_le`, `sq_le_idealTwo`, `step3_assembly_lTensor_subtype`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 6 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
