# Compactly supported algebraic integrands

This internal construction converts a compactly supported locally constant map
`f : X → V` into Mathlib's actual `MeasureTheory.SimpleFunc X V`. The domain
and target have independent universes. The target only has a zero: it carries
no topology or measurable structure. Measurable fibers require an
`OpensMeasurableSpace X`; no separation or local compactness assumption is
needed for this conversion.

The finite-image proof restricts the map to its compact topological support.
Local constancy on that compact space gives finite image. The full image is
contained in this finite image together with zero. The simple function has
exactly the original values, and each fiber is open, hence measurable. If a
measure is finite on compact sets, monotonicity bounds the measure of the
function's support by the finite measure of its compact topological support.
Thus the constructed simple function satisfies Mathlib's `FinMeasSupp`.

These are intrinsic construction lemmas preparing a finite fiber-sum integral,
not an integral definition or a Hecke action. They require no choice of a support
cover, subgroup, partition, norm, or basis in the target. Their provenance is
internal: they apply Mathlib's locally constant finite-image theorem on compact
spaces and its definitions of topological support and simple functions.
