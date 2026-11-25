# Noetherianity from adic completeness

Module `StacksFrontier.RingTheory.AdicCompletion.NoetherianRing.CompleteNoetherian`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A commutative ring complete along a finitely generated ideal is Noetherian if its quotient by that ideal is Noetherian. The file proves this by lifting generators of leading forms and applies it to an adic completion.

## Leading forms and approximation

For S with J finitely generated and S/J Noetherian, `leadingForm_core` and `exists_approx_generators` give a finite family fₖ in any ideal K, with each fₖ in the power of J of exponent dₖ. Every x in K ∩ Jᴺ can be approximated modulo the next power by a sum of sₖfₖ with sₖ in J to the power N − dₖ. The exponent uses natural-number subtraction. The helper `fg_of_approx_generators` takes this approximation property as the hypothesis `happrox`, which the preceding result supplies, and proves finite generation of K under J-adic completeness.

The existence proof takes a finite set of homogeneous generators of the submodule spanned by leading forms of K in the Noetherian graded module, then uses `component_smul_lof` to lift their coefficient relations. Iteration produces Cauchy sequences of coefficients, and completeness supplies their limits while separatedness makes the final remainder vanish.

## Completion criterion

`noetherian_of_isAdicComplete_fg` applies this to every ideal of a J-adically complete ring S with J finitely generated and S/J Noetherian. For a commutative ring R and a finitely generated ideal I with R/I Noetherian, `completion_noetherian` gives both Noetherianity of the I-adic completion R̂ and completeness along the extended ideal IR̂.

The latter theorem uses Mathlib's completeness of the completion and `completion_quot_noetherian`, which transports Noetherianity from R/I using the quotient isomorphism from evaluation at level one.

## References

The completion criterion is Tag 05GH, and its completeness input is Tag 05GG. Related references are EGA 0 7.2.6, EGA 0 7.2.8, EGA 0 7.3.1, EGA 0 7.6.11, EGA 0 7.6.18, EGA I 10.6.4, EGA I 10.8.6, EGA IV 8.11.4, SGA 3 VIIB 5.5.2, and SGA 3 X 4.0.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [05GH](https://stacks.math.columbia.edu/tag/05GH) | `completion_noetherian` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 7.2.6 | `noetherian_of_isAdicComplete_fg` | special case |
| EGA | 0 7.2.8 | `noetherian_of_isAdicComplete_fg` | sufficiency |
| EGA | I 10.6.4 | `noetherian_of_isAdicComplete_fg` | special case |
| EGA | 0 7.3.1 | `completion_noetherian` | more general |
| EGA | 0 7.6.11 | `completion_noetherian` | more general |
| EGA | 0 7.6.18 | `completion_noetherian` | partial |
| EGA | I 10.6.4 | `completion_noetherian` | special case |
| EGA | I 10.8.6 | `completion_noetherian` | special case |
| EGA | IV 8.11.4 | `completion_noetherian` | partial |
| SGA | 3 VIIB 5.5.2 | `completion_noetherian` | Noetherianity of Â |
| SGA | 3 X 4.0 | `completion_noetherian` | partial |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/AdicCompletion/NoetherianRing/CompleteNoetherian.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 10 declarations of the source file 9 are kept. The 1 left out are not needed by the results for which the extract is made: `leadingForm_fg`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 11 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
