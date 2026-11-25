# Openness of Cohen–Macaulay loci

Module `StacksFrontier.RingTheory.CohenMacaulay.OpenLocus`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a flat, finitely presented algebra `R → S`, the points of `Spec S` with Cohen–Macaulay fibre ring form an open set. The file proves this stratum by stratum in the relative dimension, and shows that the set is dense in every fibre.

## Main results

- `Algebra.isOpen_setOf_isMaximalCohenMacaulay_fiber_and_relativeDimensionAt_eq` proves that the locus where the fibre ring is Cohen–Macaulay and the relative dimension is a fixed `d : ℕ` is open.
- `Algebra.isOpen_setOf_isMaximalCohenMacaulay_fiber_and_dense_fiber` proves openness of their union in `Spec S` and density of its intersection with every fibre, in the subspace topology.

`fiberRingEquiv` identifies the quotient `S_q/pS_q` in any model of the localization with the localization of `S/pS` at the image of `q`, where `p` is the contraction of `q`. Helpers identify this ring with a localization of the residue field base change and show that finite type relative dimensions are natural numbers. `Module.isMaximalCohenMacaulay_self_of_ringKrullDim_eq_zero` gives Cohen–Macaulayness of any zero-dimensional local ring.

## Proof idea

Near a point of the stratum of dimension `d`, a principal localization admits a quasi-finite map from a polynomial ring in `d` variables, so `flat_localization_iff` identifies the stratum with the open flat locus by the field and fibrewise flatness criteria. Density comes from dimension zero at minimal points in each fibre.

## Scope

The module docstring also announces the openness and density of the Cohen–Macaulay locus of a finite type algebra over a field (Tags 00RF and 00RG) and the product splitting of Tag 00RL; this file does not contain them.

## References

Tag 00RH and Tag 00RI. EGA IV 1.3.10, 12.1.1 (vi), and 12.1.7 (iii), and SGA 4 XVIII 2.3.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [00RH](https://stacks.math.columbia.edu/tag/00RH) | `Algebra.isOpen_setOf_isMaximalCohenMacaulay_fiber_and_relativeDimensionAt_eq` | The fibre ring `S_𝔮/𝔭S_𝔮` is `Localization.AtPrime` of the image of `𝔮` in `S/𝔭S`, `𝔭 = 𝔮.under R`, as in 00RK; Cohen-Macaulayness of a local ring (Definition 00N8) is `Module.IsMaximalCohenMacaulay A A`, and `dim_𝔮(S/R)` is `Algebra.relativeDimensionAt R 𝔮`. |
| [00RI](https://stacks.math.columbia.edu/tag/00RI) | `Algebra.isOpen_setOf_isMaximalCohenMacaulay_fiber_and_dense_fiber` | The fibre ring is `Localization.AtPrime` of the image of `𝔮` in `S/𝔭S`, as in 00RH and 00RK. The fibre over `𝔭` is the subspace `comap (algebraMap R S) ⁻¹' {𝔭}` of `Spec S` and density is for its subspace topology; openness is asserted in all of `Spec S`, which implies openness in each fibre. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 1.3.10 | `essentiallyOfFinitePresentation_localRingHom` | partial |
| EGA | IV 12.1.7 | `Algebra.isOpen_setOf_isMaximalCohenMacaulay_fiber_and_relativeDimensionAt_eq` | (iii) |
| SGA | 4 XVIII 2.3 | `Algebra.isOpen_setOf_isMaximalCohenMacaulay_fiber_and_dense_fiber` | affine case |
| EGA | IV 12.1.1 | `Algebra.isOpen_setOf_isMaximalCohenMacaulay_fiber_and_dense_fiber` | (vi), affine, F=O_X |
| EGA | IV 12.1.7 | `Algebra.isOpen_setOf_isMaximalCohenMacaulay_fiber_and_dense_fiber` | (iii), affine flat |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/CohenMacaulay/OpenLocus.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 24 declarations of the source file 19 are kept. The 5 left out are not needed by the results for which the extract is made: `Algebra.exists_algEquiv_pi_of_isMaximalCohenMacaulay_fiber`, `PrimeSpectrum.isOpen_and_dense_setOf_isMaximalCohenMacaulay_localization`, `PrimeSpectrum.isOpen_setOf_isMaximalCohenMacaulay_localization`, `dense_of_minimalPrimes_subset`, `isMaximalCohenMacaulay_fiberRing_iff_of_field`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 5 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
