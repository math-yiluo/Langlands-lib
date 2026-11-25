# Tate's theorem for a principal prime quotient

Module `StacksFrontier.RingTheory.Nagata.Tate`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file proves that the Japanese property N-2 ascends from a principal prime quotient of an adically complete normal domain. N-2 means that the integral closure in every finite extension of the fraction field is a finite module over the domain.

`IsJapaneseRing.of_quotient_span_singleton` gives `IsJapaneseRing R` when R is a Noetherian integrally closed domain, x generates a prime ideal, R is x-adically precomplete, and `h` asserts `IsJapaneseRing (R ⧸ Ideal.span {x})`.

The purely inseparable criterion reduces the proof to finite purely inseparable extensions L of K = Frac(R); for each, q is a power of the exponential characteristic of K such that every q-th power in L lies in K. After adjoining a q-th root y of x, the integral closure S has a prime yS over xR. To lift independence modulo yS to independence over K, the proof clears denominators and cancels common powers of x. This bounds the residue field degree, so the Japanese property of R/xR and Noetherianity make S/yS finite. The y-adic filtration then gives finiteness modulo xS, and adic lifting gives finiteness of S. The original integral closure embeds as a submodule.

The completeness hypothesis is `IsPrecomplete (Ideal.span {x}) R`. Separatedness follows from Noetherianity and the properness of the ideal. Normality here is Mathlib's `IsIntegrallyClosed R` for a domain.

Stacks Project Tag 032P, with Tag 032N for the purely inseparable criterion and Tag 031D for adic lifting. EGA 0 23.1.3.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [032P](https://stacks.math.columbia.edu/tag/032P) | `IsJapaneseRing.of_quotient_span_singleton` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 23.1.3 | `IsJapaneseRing.of_quotient_span_singleton` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Nagata/Tate.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
