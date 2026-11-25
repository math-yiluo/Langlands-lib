# N-1 and N-2 for polynomial rings

Module `StacksFrontier.RingTheory.Nagata.Polynomial`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file proves that the two finiteness conditions on integral closures ascend from a domain to its polynomial ring in one variable. N-1 concerns the fraction field itself. N-2, also called the Japanese property, concerns finite extensions of that field.

`Polynomial.isN1_and_isJapaneseRing` packages two implications. For a domain R, `StacksIsN1 R` implies `StacksIsN1 (Polynomial R)`. If R is also Noetherian, `IsJapaneseRing R` implies `IsJapaneseRing (Polynomial R)`. The proof is packaged as `Stacks.Nagata.PolynomialAscent.solution`.

For N-1, if R′ is the integral closure of R in its fraction field, then R′[X] embeds into the fraction field of R[X]. Its image is integrally closed, finite over R[X], and has the same fraction field, so it is the required integral closure. For N-2, the purely inseparable criterion reduces the proof to finite purely inseparable extensions of Frac(R[X]). Inside an algebraic closure, inverse Frobenius puts such an extension inside the fraction field of R′[Y], where R′ is the integral closure of R in a finite extension of Frac(R) and Y raised to a common power q is X. The Japanese hypothesis makes R′ finite over R, and the equation for Y makes R′[Y] finite over R[X]. The Noetherian hypothesis lets the desired integral closure inherit finiteness as a submodule.

The private helper for polynomial expansion, `module_finite_polynomial_of_expand`, uses the algebra structure specified by `halg`, which sends X to X raised to q and acts on coefficients through R → S. It requires q ≠ 0 and module-finiteness of S over R. The implementation notes of the module docstring still describe a second expansion helper, for the integral closure, which is not in the file. The N-2 test fields are in the universe of R, which is also the universe of R[X].

Stacks Project Tag 032O and Tag 032N. The inseparable step is a special case of EGA II 6.3.10.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [032O](https://stacks.math.columbia.edu/tag/032O) | `Polynomial.isN1_and_isJapaneseRing` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | II 6.3.10 | `module_finite_integralClosure_of_isPurelyInseparable` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Nagata/Polynomial.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 11 declarations of the source file 10 are kept. The 1 left out are not needed by the results for which the extract is made: `Stacks.Nagata.PolynomialAscent.module_finite_integralClosure_of_expand`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
