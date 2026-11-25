# Integral closedness of formal power series

Module `StacksFrontier.RingTheory.PowerSeries.IntegrallyClosed`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file proves that formal power series in one variable over a Noetherian integrally closed domain are integrally closed in their own fraction field.

`PowerSeries.instIsIntegrallyClosed` supplies `IsIntegrallyClosed R⟦X⟧` for a Noetherian integrally closed domain R. The key private divisibility lemma, `dvd_of_forall_pow_dvd_pow_succ`, shows that if h is nonzero and hⁿ divides sⁿ⁺¹ for every natural n, then h divides s in R⟦X⟧. The other helpers compare orders, characterize the image of coefficientwise extension to the fraction field K of R, and cancel powers of X in that image.

The proof uses almost integrality to reduce an integral fraction to the divisibility lemma. Comparing orders gives s = hV in K⟦X⟧, and the divisibilities give hVⁿ over R for every n. After removing the initial power of X from h, the constant coefficient of V is almost integral over R and hence lies in R. Subtracting that coefficient and dividing by X preserves the condition, so induction recovers every coefficient.

The instance supplies the integral-closedness part of Tag 0BI0. The domain and Noetherian instances for the series ring come from Mathlib. Noetherianity of R is used to pass from almost integrality to integrality for coefficients. The order comparison takes place in power series rings.

The almost-integrality references are Tag 00GW and Tag 00GX. The comments also cite Tag 0306 among the source’s references. The table of references below also gives EGA IV 21.13.9 (iv).

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0BI0](https://stacks.math.columbia.edu/tag/0BI0) | `instIsIntegrallyClosed` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 21.13.9 | `instIsIntegrallyClosed` | (iv) |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/PowerSeries/IntegrallyClosed.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
