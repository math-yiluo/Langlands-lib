# Rational loci and their actual bounded restriction maps

Author: Worker 36.

Fix a complete ultrametric normed field K and a presented strict affinoid
algebra P. The objects of the constructed category are the existing
`RationalData K P`: a finite denominator/numerator tuple in P with no
common spectrum zero. An `Inclusion d e` is an inclusion of the actual
unit-radius rational loci, from `d.locus` to `e.locus`. Identity and
composition are identity and transitivity of subset inclusion. Each hom
set is a subsingleton, so the category laws follow from proof irrelevance.
The objects retain their input presentations: equal loci can come from
distinct rational data, and this category does not identify those objects.
The inclusion category alone does not require completeness; the bounded
restriction constructions below use the complete coefficient field.

Each object already has a constructed algebra `d.algebra`, the actual
closed-ideal Tate quotient, and a bounded structural map `d.baseMap` from P.
The published theorem `StrictTestDomain.rationalRepresentation` proves its
strict-test universal property from the input data.
`baseMap_hasImageIn` extracts the image-containment consequence.
For an inclusion h from d to e, `Inclusion.existsUnique_restriction` applies
the representation property of e to the actual quotient algebra of d.
It gives a unique bounded K-algebra map from `e.algebra` to `d.algebra`
whose composite with `e.baseMap` is `d.baseMap`. This map is derived from
representability, which is already proved for these concrete quotients;
no map or additional representation assumption is supplied by the caller.

`Inclusion.restriction` chooses this unique bounded map.
`restriction_comp_baseMap` proves its required equation, and
`restriction_unique` expresses uniqueness among maps satisfying that
equation. `restriction_id` identifies the restriction for an identity
inclusion with the bounded identity. `restriction_comp` identifies the
restriction for a composite inclusion with the composite bounded maps in
the contravariant order. Both laws follow by checking the equation over P
and applying uniqueness. `spectrumMap_restriction` evaluates the equation
at a multiplicative seminorm, proving commutation of the induced spectrum
map with the maps to M(P).

Conversely, `subset_of_restriction` proves inclusion of the loci from any
bounded map between the quotient algebras satisfying the equation over P.
A point in the smaller locus lifts to its quotient spectrum by the exact
image theorem. Pulling that point back along the bounded map and using
the equation over P places the original point in the other locus.
`inclusionEquivRestriction` combines this with uniqueness to construct an
equivalence between inclusions and bounded maps over P. It does not equate
inclusions with arbitrary bounded maps lacking that equation.

`toAffinoidSpace` sends d to the opposite-category object of its actual
quotient algebra and h to the opposite of its restriction map. The two
restriction laws prove the functor laws. `toTopologicalSpace` composes this
with the existing multiplicative-spectrum functor. Thus its objects and
maps are genuine spectra and continuous seminorm pullbacks.

All objects and algebras use the coefficient universe. Rational radii are
one, and the represented-domain theorem used here tests all presented
strict affinoids. Empty numerator tuples, empty loci, zero and nonreduced
quotients, and trivial scalar valuations remain permitted. The source's
unrestricted affinoid-domain property requires all affinoid tests; this
module does not extend the test class. It defines neither coverings nor
a structure sheaf, a Grothendieck topology, atlas gluing, or an analytic
etale site.

This is a derived categorical construction from Berkovich,
*Non-archimedean analytic spaces*, Trieste lectures (2009), Definition
2.1.11 on printed/PDF p. 8 and Definition 2.2.1 and Exercise 2.2.2(ii) on
printed/PDF p. 9. The registered original is
`berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The first definition fixes the opposite bounded-algebra category. The
domain universal property in the second definition induces restriction
maps for inclusions, and its uniqueness gives the functor laws. The
exercise supplies the rational input and quotient equations, specialized
here to unit radii. This precise category of chosen rational input data
and the displayed correspondence are derived from those constructions;
they are not separately named results in the source. Its only project
import is the published rational representation proof and its existing
dependency chain.
