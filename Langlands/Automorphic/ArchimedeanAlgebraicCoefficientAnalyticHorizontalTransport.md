# Full automorphic maps on actual analytic coefficient cohomology

Fix the full original analytic coefficient carrier `AnalyticSpace e ρ`. A full
automorphic intertwiner `L : S.Intertwiner T` acts on the automorphic tensor
factor and fixes the coefficient factor. `tensorAnalyticIntertwinerReducedLieHom`
restricts the published full tensor Lie map to the actual reduced Lie algebra.
Its value on `f ⊗ v` is `L f ⊗ v`. The compact tensor map has that same
underlying linear map. `tensorAnalyticHorizontalMap` restricts postcomposition
by this map to the existing full compact horizontal cochains and intertwines
their existing finite adelic representations.

The chain equation `tensorAnalyticHorizontalMap_differential` follows from
coefficient differential functoriality for the genuine reduced Lie map. The
existing generic cycle and quotient transport then defines
`tensorAnalyticHorizontalCyclesMap` and `tensorAnalyticHorizontalCohomologyMap`
on the actual differential kernels and the existing cycle quotients. The value
and class formulas describe the transported representative; the quotient
projection is natural as a bundled finite adelic intertwiner.

Cochain identity and composition follow from the tensor-product linear-map
laws. The generic congruence helpers in
`HorizontalCohomologyIntertwinerLaws` carry those actual cochain equalities
to both cycles and cohomology. All three levels therefore preserve identity
and composition as equalities of bundled finite adelic intertwiners.

The cycle value, quotient class, quotient-projection naturality, and cycle
and quotient identity/composition declarations are inferred-type
abbreviations of the specialized generic proofs. Their conclusions use the
generic definitions underlying the named actual maps and representations;
these are definitionally the same objects. This preserves the formulas
without restating and rechecking large definitionally equal target types.
The abbreviations add no assumptions.

All natural degrees, the entire original coefficient carrier, independent
number-field universe, empty finite index types and both complex-place
orientations are retained. The reduced Lie map and cochain laws hold in all
ranks. The differential, cycle and quotient constructions retain the explicit
`NeZero n` premise of the published analytic horizontal complex. Analytic
coefficients here use the published real Fréchet-calculus realization; this
unit adds no power-series analyticity, occurrence or nonvanishing claim.

This is an internal construction from the published actual analytic horizontal
complex, automorphic tensor maps and generic horizontal cohomology transport.
Its construction parallels the algebraic coefficient transport, with the
original analytic coefficient action throughout. Every chain compatibility
needed for descent is proved, rather than required as extra data. No new
original-literature identification is asserted.
