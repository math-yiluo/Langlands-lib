# Orientation of linked segments

`Langlands.Classification.SegmentLinkageOrientation` states that two linked
segments have a precedence relation in at least one direction. It quantifies
over every prime, every supplied p-adic field and topology datum, and every pair
of segments, with independent field and representation universes.

The imported definition of `Segment.IsLinked` requires that neither support
contains the other and that their union is the support of a segment.
`Δ.Precedes Γ` requires linkage and an equality
`Γ.base = Δ.base.twist (k : ℝ)` for a positive natural number `k`.
The conclusion is the disjunction of the two possible directions.
It asserts neither exclusivity nor uniqueness of the positive shift.

This is an internal, derived statement about the existing finite support and
twist definitions in `Segments`. It does not introduce another notion of
linkage and makes no new claim of correspondence with external literature.
Its intended elementary argument compares the positions of the two bases in
a segment realizing the union. Equal bases would force support containment by
comparing lengths. Unequal positions supply a positive difference, and the
twist addition law supplies the required base equality. This argument does
not require injectivity of the real twist action.

This file defines a proposition only. A proof requires separate validation
and independent review. The statement does not assert square-integrability,
unitarizability, strict comparison of exponents, or any classification result.
