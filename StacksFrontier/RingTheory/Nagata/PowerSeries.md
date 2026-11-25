# The Japanese property for formal power series

Module `StacksFrontier.RingTheory.Nagata.PowerSeries`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let R be a Noetherian domain with the Japanese property N-2. This file shows that the integral closure of its one-variable formal power series ring in each finite extension of its fraction field is finite over that power series ring.

`PowerSeries.isJapaneseRing` takes `IsJapaneseRing R` explicitly and gives `IsJapaneseRing R⟦X⟧`. The auxiliary theorem `Stacks.Nagata.PowerSeriesAscent.module_finite_powerSeries` shows that for a commutative A-algebra B finite as an A-module, B⟦X⟧ is finite over A⟦X⟧. A finite generating set for B works again, by choosing coefficients independently at each degree.

The proof takes R′ to be the integral closure of R in its fraction field. Integrality and the common fraction field pass N-2 to R′, which is finite over R and is therefore Noetherian. Tate's theorem applies to the normal, X-adically complete ring R′⟦X⟧ because the prime ideal (X) has quotient R′. The finite extension R⟦X⟧ → R′⟦X⟧ then gives descent of N-2.

The theorem states the N-2 part of Tag 032Q. The domain and Noetherian conclusions are supplied by Mathlib instances. The test fields in `IsJapaneseRing` live in the universe of the ring, which is also the universe of its power series ring.

Stacks Project Tag 032Q, Tag 032P (Tate's theorem), and Tag 032K (finite descent). EGA 0 23.1.3 and EGA 0 23.1.4, the latter in the one-variable case.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [032Q](https://stacks.math.columbia.edu/tag/032Q) | `isJapaneseRing` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 23.1.3 | `isJapaneseRing_powerSeries` | A = R[[T]], x = T |
| EGA | 0 23.1.4 | `isJapaneseRing` | case r = 1 |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Nagata/PowerSeries.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 2 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
