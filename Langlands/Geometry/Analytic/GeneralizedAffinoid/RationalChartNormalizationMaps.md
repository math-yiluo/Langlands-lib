# Actual maps to normalized strict rational quotients

This internal construction combines `RationalChart.ringEvaluate` with
`RationalChart.normalizedStrict`. The coefficient fields `K : Type u` and
`L : Type v` have independent universes. Both are complete ultrametric normed
fields. The source is any presented positive-polyradius affinoid algebra `A`,
the target base is any presented strict affinoid algebra `Q` over `L`, and
`ψ : BoundedRingHom A Q` is contractive. No scalar extension tower is supplied.
For a rational chart `d`, choose `τ j : L` with `‖τ j‖ = d.radii j`.

`normalizedStrictMap` is a contractive bounded ring homomorphism from the actual
weighted closed-ideal quotient `d.algebra` to the actual quotient of
`d.normalizedStrict Q ψ τ hτ`. Its base-map formula is
`F (d.baseMap a) = normalized.baseMap (ψ a)`. Its image of the original fraction
is `τ j` times the normalized strict fraction. These are proved as
`normalizedStrictMap_baseMap` and `normalizedStrictMap_fraction`;
`norm_normalizedStrictMap_le` proves contraction for the quotient norms.

The supporting strict `RationalPresentation.norm_baseMap_le` chooses Tate-series
representatives arbitrarily close to the quotient norm. Adjoining variables is
contractive by the published strict evaluation bound, and projection to the
rational quotient is contractive. The same bound for
`RationalLocalization.baseMap` follows by its relation-model equivalence, whose
norm preservation follows by elimination of the presentation equality. Actual
strict fraction coordinates have norm at most one by quotient projection of a
Tate coordinate. Multiplication by `τ j` therefore has the required radius
bound. Positivity makes `τ j` nonzero; multiplying the normalized denominator
equation by this scalar cancels its inverse. The published weighted ring
evaluator then constructs `normalizedStrictMap` and supplies all its formulas
and its norm bound.

The quotient norm estimates do not require proper ideals or nonzero target
quotients. The coordinate tuples may be empty. This is internal quotient-map
preparation for scalar descent and makes no gluing assertion. The proof route
is derived from the imported evaluator, strict quotient presentation and
normalization definitions, rather than a new assertion attributed to the
literature.
