# Coefficient pullback preserves finite limits of actual rational charts

Author: Worker 56.

Let K be an ultrametric normed field, let A and B be actual presented
positive-radius affinoid algebras, and let `φ : A → B` be an arbitrary
bounded K-algebra homomorphism. The chosen chart pullback retains the
finite arity and positive radii and chooses scalar-series representatives
of the mapped coefficient classes.

The all-products intersection of two charts d and e uses denominator
`g * h` and every product of their denominator-extended numerator tuples,
with product radii. Multiplicativity of the presentation maps and φ
proves equality of the denominator coefficient classes in the direct
pullback of this intersection and the intersection after pullback.
For the numerator classes, split each of the two extended finite indices
into its denominator or numerator case. The existing coefficient-class
formulas prove equality in each case. Arities and radii coincide
definitionally.

`pullbackInterIso` constructs both arrows between these charts using the
published bounded `representativeMap` on the actual closed rational
quotients. Its base-map formula proves both equations over B. The proved
uniqueness of actual bounded restrictions gives the inverse laws.
`pullbackWholeIso` uses the same construction on the empty numerator tuple:
φ sends the coefficient class of one to one, and there are no numerator
conditions. These two object isomorphisms require no completeness
assumption.

Now assume K is complete. The comparison with the intersection commutes
with both actual projection arrows, again by proved uniqueness of
bounded restrictions. For any cospan of actual chart arrows, the image
of its constructed intersection pullback cone is a limit cone:
given an arbitrary cone over the image cospan, first apply the published
bounded intersection lift over B, then compose with the inverse of
`pullbackInterIso`. This constructs the required actual arrow into the
image cone vertex. Proved uniqueness supplies both projection equations
and the universal uniqueness. This is
`pullbackInterPullbackConeIsLimit`; it establishes preservation of the
specific cospan limit and then of all pullbacks through Mathlib.

The actual whole chart over B is terminal. Its isomorphism with the
pullback of the whole chart over A proves that the latter is terminal,
so the pullback functor preserves the empty limit. Mathlib's theorem
that preservation of terminal objects and pullbacks implies preservation
of finite limits supplies `pullbackFunctor_preservesFiniteLimits`.
No limit-preservation property or missing comparison arrow is an input.

These are limits in the fixed-base category of actual chosen rational
charts and bounded restrictions. The coefficient functor changes the
fixed base from A to B. The construction allows arbitrary positive radii,
empty numerator tuples, trivial valuations, zero or nonreduced quotients
and empty spectra. It does not assert arbitrary affinoid-space products,
an arrow from every locus inclusion, full analytic-domain factorization,
structure-sheaf descent, analytic atlases or etale sites.

Source context: Berkovich, *Non-archimedean analytic spaces*, Trieste
lectures (2009), printed/PDF p.8, Definition 2.1.11 for bounded maps
and opposite affinoid-space direction; p.9, Definition 2.2.1 and
Exercise 2.2.2(ii)–(iii) for arbitrary positive-radius rational quotients
and intersections; p.10, Fact 2.2.3(i) for the representing spectrum.
Registered source `berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The comparison maps and categorical preservation assertions are internal
consequences of the representative-map, coefficient-pullback
and chart-limit constructions, rather than separately numbered source
theorems. Explicit coefficient unit generation is retained without
claiming equivalence to absence of common spectral zeros.
