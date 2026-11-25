# Vanishing differentials over a perfect field

Module `StacksFrontier.RingTheory.Kaehler.PerfectField`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Over a perfect field of prime characteristic p, the elements of a field extension with zero universal differential form the subfield of p-th powers.

`KaehlerDifferential.D_eq_zero_iff_exists_pow_eq`, proved as `Stacks.KaehlerDifferential.PthPowers.solution`, says that for a perfect field k of characteristic p and a field extension K/k, `KaehlerDifferential.D k K a = 0` is equivalent to the existence of b in K with bᵖ = a. The theorem applies to arbitrary field extensions of k. The hypotheses on the base include `PerfectField k`, `Fact p.Prime` and `CharP k p`. The characteristic of K follows from the base.

The power rule shows that every p-th power has zero differential. For the converse, perfection makes the Frobenius image Kᵖ an intermediate field. The proof passes to differentials over Kᵖ and uses the exponent-one case. There, a maximal intermediate field avoiding a given element, obtained by Zorn's lemma, makes the remaining extension simple of degree p. If the differential of its generator vanishes, all differentials vanish, so the purely inseparable extension is formally unramified and must be trivial.

References include Tag 031W and EGA 0 21.1.6, 21.4.4, and 21.4.6.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [031W](https://stacks.math.columbia.edu/tag/031W) | `KaehlerDifferential.D_eq_zero_iff_exists_pow_eq` | The source's `d a = 0 in Ω_{K/k}` is `KaehlerDifferential.D k K a = 0` and `a` is a `p`-th power is `∃ b, b ^ p = a`; characteristic `p > 0` is `[Fact p.Prime] [CharP k p]` on the base. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 21.1.6 | `surjective_algebraMap_of_D_eq_zero` | Field case |
| EGA | 0 21.4.4 | `D_eq_zero_iff_mem_bot` | special case |
| EGA | 0 21.4.4 | `KaehlerDifferential.D_eq_zero_iff_exists_pow_eq` | more general |
| EGA | 0 21.4.6 | `KaehlerDifferential.D_eq_zero_iff_exists_pow_eq` | (a) ⇔ (b), special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Kaehler/PerfectField.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 4 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.
