# Degree zero of the original horizontal cohomology quotient

This internal construction identifies the existing horizontal cohomology in
degree zero with actual simultaneous invariant vectors. It uses the original
restricted Chevalley–Eilenberg differential, its kernel, and its boundary
quotient from `HorizontalCohomology`; it does not define a replacement complex.

The coefficient field has characteristic zero. The Lie algebra, coefficient
module, and group have independent universe parameters. Inputs are the existing
representations `σ` on the Lie algebra and `ρ` on the coefficient module, the
chosen horizontal submodule `H`, bracket covariance, coefficient covariance,
and the all-degree infinitesimal insertion identity needed by the original
horizontal differential. No connectedness or finite-dimensionality is assumed.

`jointInvariants` is the intersection of Mathlib's `Representation.invariants`
and the underlying submodule of `LieModule.maxTrivSubmodule`. Thus its vectors
are fixed by every group element and annihilated by every Lie algebra element.
These are the full group and the full Lie algebra, not just the horizontal
directions.

`differential_zero_apply` specializes the published coefficient differential
formula: the restricted differential of a zero cochain `f`, evaluated on a
one-tuple `x`, is the action of `x 0` on `f 0`. All zero-tuples agree.
Consequently `mem_cycles_zero_iff` characterizes the actual zero cycles by
annihilation of their value by the Lie algebra.

`cyclesDegreeZeroEquiv` restricts the existing
`HorizontalAlternating.degreeZeroEquiv` to these actual cycles. Its inverse
uses that same equivalence's constant zero cochain, with evaluation formula
`cyclesDegreeZeroEquiv_symm_apply`. The proof of
`boundariesInCycles_zero` uses the original zero-boundary definition and the
published membership characterization of boundaries inside cycles.
`degreeZeroEquiv` then composes Mathlib's quotient-by-zero equivalence with
`cyclesDegreeZeroEquiv`.

The representative formula `degreeZeroEquiv_class` evaluates the original
cycle representative. The inverse formula `degreeZeroEquiv_symm` is the
original class projection of the corresponding constant zero cycle.
`degreeZeroEquiv_symm_ne_zero` follows from injectivity of the inverse linear
equivalence and proves nonvanishing for any supplied nonzero simultaneous
invariant.

The provenance is internal: the comparison is derived directly from the
implemented differential and existing fixed-vector and quotient constructions.
No external comparison theorem, geometric realization, automorphic occurrence,
or existence of a nonzero invariant is asserted here. Concrete coefficient
modules must discharge the displayed original differential premises.
