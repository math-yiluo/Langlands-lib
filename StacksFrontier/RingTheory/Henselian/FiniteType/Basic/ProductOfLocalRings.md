# Finite local factors over a henselian base

Module `StacksFrontier.RingTheory.Henselian.FiniteType.Basic.ProductOfLocalRings`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Over a henselian local ring R with maximal ideal 𝔪, idempotents of the closed fibre of a finite algebra lift to the algebra. This gives a decomposition of a finite algebra into finitely many local factors.

## Main results

- For a module-finite R-algebra A, `henselian_lift_single_idem` lifts an idempotent from A/𝔪A to A. `henselian_lift_coi` lifts a finite complete orthogonal family, preserving pairwise orthogonality and the sum 1.
- `exists_completeOrthogonalIdempotents_lift` chooses such a family in A with local quotients A/(1 − eᵢ). `exists_algEquiv_pi_isLocalRing` uses it to express A as a finite product of local, module-finite R-algebras.

A single lift joins primitive idempotents obtained by étale descent, and the family lift adjusts single lifts by complementary idempotents. Locality of each factor follows from locality of its closed fibre and integrality over R.

In `fibre_idempotent_lift_of_primitive`, the hypothesis `hprim` assumes an isolating idempotent at every prime over 𝔪. The henselian proof supplies it by `reduction_of_isolating_idem`. In `henselian_lift_coi_of_single`, the hypothesis `hsingle` assumes the single-idempotent lifting result and is discharged by `henselian_lift_single_idem`. The lifting lemmas and the module-finite decomposition take R in `Type u` and A in `Type (max u v)`, so the universe of A must be at least that of R. The module docstring also announces the decomposition of a finite type algebra (Tag 04GJ), which is not in the file.

## References

The finite-algebra decomposition condition of Tag 04GG, also given as a forward implication in EGA IV 18.5.9 and SGA 4 VIII 4.1. The closed-fibre argument refers to Tag 00E5, Tag 00EE, Tag 00EC, and Tag 00UJ. See also EGA IV 18.5.11, SGA 1 I 6.2, SGA 3 V 4.1.2, SGA 3 VIIB 2.9, SGA 3 XV 3.9, and SGA 3 XXIV 8.1.2.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 1 I 6.2 | `henselian_lift_coi` | partial |
| SGA | 3 V 4.1.2 | `lifted_factor_isLocalRing` | (F), special case |
| SGA | 3 XXIV 8.1.2 | `lifted_factor_isLocalRing` | partial |
| EGA | IV 18.5.11 | `exists_completeOrthogonalIdempotents_lift` | (F), partial |
| EGA | IV 18.5.9 | `exists_completeOrthogonalIdempotents_lift` | (ii), necessity |
| SGA | 3 VIIB 2.9 | `exists_completeOrthogonalIdempotents_lift` | Finite-dimensional case |
| SGA | 3 XV 3.9 | `exists_completeOrthogonalIdempotents_lift` | partial |
| SGA | 4 VIII 4.1 | `exists_completeOrthogonalIdempotents_lift` | (i) |
| EGA | IV 18.5.9 | `exists_algEquiv_pi_isLocalRing` | (ii), necessity |
| SGA | 4 VIII 4.1 | `exists_algEquiv_pi_isLocalRing` | (i), forward direction |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Henselian/FiniteType/Basic/ProductOfLocalRings.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 9 declarations of the source file 8 are kept. The 1 left out are not needed by the results for which the extract is made: `exists_algEquiv_prod_of_henselianLocalRing`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 10 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
