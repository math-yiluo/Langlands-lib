# Haar probability measure on `U(n)`

Module: `Langlands.Representation.Archimedean.ComplexDuality.UnitaryHaar`.

## Purpose and provenance

This is internal infrastructure for the proof of
`Langlands.Archimedean.ComplexStandardDualityStatement`. That proof pairs functions on
`GL_n(ℂ)` by integrating over the unitary group `U(n)` (`unitaryCompact ℂ n`, the subgroup of
`Langlands.GeneralLinear n ℂ` of unitary matrices). This module supplies the measure: the
normalized Haar measure of the compact group `U(n)`, which is left and right invariant.
Everything here is standard measure theory on compact groups, stated for the Library's
`unitaryCompact ℂ n`, so the module cites no literature.

## Proof route

`U(n)` is the image of the compact group `Matrix.unitaryGroup (Fin n) ℂ` under the continuous
map `Unitary.toUnits`, so it is compact. The measure is Mathlib's `Measure.haarMeasure` for the
whole space, viewed as a positive compact set, so the whole space has measure `1`. Right
invariance holds because a right translate of a Haar probability measure is again a Haar
probability measure, and Mathlib's `Measure.isHaarMeasure_eq_of_isProbabilityMeasure` says two
such measures are equal. On a compact space every continuous function has compact support.
Integrability of continuous functions and positivity of the integral of a nonzero continuous
nonnegative function then come from the corresponding Mathlib lemmas for compactly supported
functions; positivity uses that a Haar measure charges every nonempty open set.

## Declarations

All declarations are in the namespace `Langlands.Archimedean.ComplexDuality`.

- `unitaryCompact_eq_range n`: as a set, `unitaryCompact ℂ n` is the range of
  `Unitary.toUnits` on `Matrix.unitaryGroup (Fin n) ℂ`.
- `isCompact_unitaryCompact n`: `unitaryCompact ℂ n` is a compact subset of `GL_n(ℂ)`.
- `compactSpace_unitaryCompact n` (instance): `unitaryCompact ℂ n` is a compact space.
- `unitaryMeasurableSpace n`, `unitaryBorelSpace n` (scoped instances, active only inside the
  namespace `Langlands.Archimedean.ComplexDuality`): the Borel σ-algebra on
  `unitaryCompact ℂ n`. They are scoped so that they cannot clash with σ-algebras that other
  developments might put on the same type.
- `unitaryHaar n` (definition): the Haar probability measure on `unitaryCompact ℂ n`.
- Instances: `unitaryHaar n` is a probability measure, a Haar measure, left invariant
  (`IsMulLeftInvariant`) and right invariant (`IsMulRightInvariant`).
- `integrable_unitaryHaar`: a continuous function from `unitaryCompact ℂ n` to a normed group
  is integrable for `unitaryHaar n`.
- `integral_unitaryHaar_pos`: a continuous nonnegative real function on `unitaryCompact ℂ n`
  that is nonzero at some point has positive integral for `unitaryHaar n`.
