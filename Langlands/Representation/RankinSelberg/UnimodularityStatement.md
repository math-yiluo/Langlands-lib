# Intrinsic all-rank Haar unimodularity obligations

Worker 114 states two propositions in `Langlands.RankinSelberg`:
`GeneralLinearHaarRightInvariantStatement` and
`UnipotentHaarRightInvariantStatement`. They are independent proof targets
for the existing normalized left Haar measures. This module supplies the
statements only.

Both declarations take an arbitrary `F : Type uF`, with the universe `uF`
explicit, and instances of `Field F`, `ValuativeRel F`, `TopologicalSpace F`,
and `IsNonarchimedeanLocalField F`. Each takes every natural number `n`;
the group's rank is `n + 1`, so `n = 0` is rank one. Each statement requires
only a measurable space and Borel compatibility on its own group, in addition
to those field hypotheses. Neither requires a measurable space on `F` or
measurable and Borel structures on the other group.

`GeneralLinearHaarRightInvariantStatement F n` is exactly
`MeasureTheory.Measure.IsMulRightInvariant (generalLinearHaar F n)`.
Its group is `Matrix.GeneralLinearGroup (Fin (n + 1)) F`.
`UnipotentHaarRightInvariantStatement F n` is exactly
`MeasureTheory.Measure.IsMulRightInvariant (unipotentHaar F n)`.
Its group is the actual subgroup `GeneralLinear.upperUnipotent (n + 1) F`,
viewed as a type. In pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`,
`Mathlib/MeasureTheory/Group/Defs.lean` defines this class in namespace
`MeasureTheory.Measure`: for every group element `g`, mapping the measure
under `fun x => x * g` returns the same measure. The declarations use this
class directly.

The provenance is internal and derived from the published
`Langlands.Representation.RankinSelberg.Measures` interface. That module
constructs `generalLinearHaar F n` with the integral general-linear subgroup
of mass one and `unipotentHaar F n` with the integral upper-unipotent subgroup
of mass one. It already supplies their `IsHaarMeasure` and `Regular`
instances. The new propositions ask for right invariance of those exact
measures, so their proofs will establish the two-sided invariance needed by
the compatible quotient-measure construction. This specialization is an
internal obligation; no claim is made that an original source states these
Lean declarations or these particular project normalizations.

No measure definition or normalization is changed. The statements assume
neither right invariance nor unimodularity, an Iwasawa decomposition, or the
existence of a quotient measure. They contain no implication from either
target back to itself. The published `RankOneQuotient` module proves the
rank-one instances, but it is not imported here and does not replace the
all-rank targets. Independent proofs of the two propositions and construction
of a compatible quotient measure are subsequent tasks.
