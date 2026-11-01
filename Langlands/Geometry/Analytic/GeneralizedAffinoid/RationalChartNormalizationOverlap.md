# Normalization and actual overlap restrictions

This internal construction works over independent complete ultrametric normed
fields `K : Type u` and `L : Type v`. Let `A` be a positive-polyradius presented
affinoid algebra, `Q` a presented strict affinoid algebra over `L`, and
`ψ : BoundedRingHom A Q` a contractive coefficient map. For two actual rational
charts `d` and `e`, choose scalars `τ j` and `υ j` whose norms equal their
respective relative radii.

`normalizedStrictOverlapMap` constructs a bounded ring homomorphism from the
actual quotient of `d.inter e` to the actual strict quotient of the intersection
of `d.normalizedStrict Q ψ τ hτ` and `e.normalizedStrict Q ψ υ hυ`. The map
commutes with the structural maps from `A` through `ψ`. Both restriction squares
commute: applying the overlap map after either original restriction equals
applying the corresponding normalized chart map followed by the published
strict intersection restriction.

The public theorem `normalizedStrictMap_compatible` consequently carries any
pair of compatible original quotient elements to a compatible pair in these
strict quotients. Its hypothesis is equality after the actual published
`RationalChart.interLeft` and `interRight` restrictions; its conclusion is
equality after the actual published `StrictTestDomain.RationalData.interLeft`
and `interRight` restrictions. It assumes no gluing operator or descent result.

For the construction, extend each realizing scalar tuple by scalar one at the
denominator entry. The product of two extended scalars realizes exactly the
published product radius at the corresponding pair of indices. A case split on
the extended index expresses each normalized extended numerator as the original
mapped numerator times the inverse scalar. Multiplicativity of the coefficient
maps and inverse products then identifies the strict rational input obtained by
normalizing `d.inter e` with the strict intersection of the normalized inputs.
Transport along this equality gives a bounded algebra map between their actual
quotients. Composing it with the existing `normalizedStrictMap` for `d.inter e`
gives `normalizedStrictOverlapMap` and its base-map formula.

For each restriction square, the two composites are bounded ring maps from the
same original chart quotient. Their common coefficient map is contractive by
strict base-map contraction and the contraction of `ψ`. The published
`ringHom_ext_over_base` therefore identifies them using their structural-map
equations. Applying the resulting overlap map to the compatibility hypothesis
proves the public theorem. No formula for an arbitrarily chosen presentation
is substituted for either published restriction.

This is internal preparation derived from the imported actual quotient maps,
intersection definitions and base-map uniqueness. It makes no whole-spectrum
gluing assertion. Arbitrary positive real radii, empty coordinate tuples and
zero quotient algebras remain allowed; no nontrivial valuation, proper ideal,
nonzero quotient, or nonempty rational locus is assumed.
