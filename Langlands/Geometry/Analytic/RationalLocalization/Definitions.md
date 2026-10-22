# Rational quotients from affinoid-algebra elements

Author: Worker 36.

This module constructs a rational quotient from an arbitrary
`PresentedStrictAffinoidAlgebra K`, an element `g` of its actual quotient
carrier, and a finite tuple `f` of elements of that carrier. It does not
ask the caller to supply Tate-series representatives or a resulting
algebra.

`model` uses the presentation's own closed ideal as its relation set.
The proved equality `ofRelations_ideal` identifies this relation model
with the input presentation. `modelEquiv` transports that equality to
an actual bounded algebra equivalence. `seriesLift` chooses a Tate
series representing the inverse image of an element under this
equivalence. The two projection lemmas prove its equations in the model
and in the original algebra. No norm bound or algebra-map property of
the choice function is asserted. These helpers need no completeness.

Over a complete ultrametric normed field, `algebra` specializes the
existing enlarged Tate quotient at these chosen representatives. Its
closed relation ideal imposes the original equations and
`g Y_j - f_j`, using unit radii for the new variables. `baseMap` composes
the inverse model equivalence with the existing bounded quotient base
map. `fractionCoordinate` is the image of the corresponding new Tate
variable. The construction permits the zero quotient and empty tuples,
and requires no unit-ideal hypothesis.

`GeneratesUnitIdeal` is the proposition that the actual elements `g`
and `f_j` generate the unit ideal in the input algebra. `locus` is the
subset of its actual bounded multiplicative spectrum defined by
`x(f_j) ≤ x(g)`. These two definitions use only the original algebra
elements. Neither assumes an embedding, factorization, point lift, or
realization of the locus.

These are derived constructions for Berkovich, *Non-Archimedean
analytic spaces* (Trieste 2009), Definitions 2.1.1–2.1.2 on printed
page 7 and Exercise 2.2.2(ii) on page 9. The source uses base-algebra
elements and a relative-series quotient. Here the already constructed
finite Tate quotient and its genuine surjective projection supply the
representatives. The relative-series identification, arbitrary radii,
and the full analytic-domain property of Definition 2.2.1 are separate
obligations. The companion statement concerns spectrum identification,
bounded extension, and transport; this construction pair does not
prove those conclusions.

Registered original: `berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
