# Comparison of the actual strict and relative binary Laurent diagrams

Authors: Worker 84 and Worker 101.

The theorem assembles the published strict-to-relative rational
comparison, the relative four-to-two-variable overlap comparison and the
elementary binary compatibility lemmas into the exact diagram comparison.

## Exact target and objects

The declaration is
`Langlands.Analytic.StrictTestDomain.binaryLaurentDiagramComparison.{u}`.
Its explicit type is exactly the already published
`BinaryLaurentDiagramComparisonStatement.{u}`. The proof introduces every
quantifier of that proposition: a complete ultrametric normed field
`K : Type u`, an actual presented strict affinoid algebra `P`, and
`f : P`. There is no further parameter or assumption in the declaration.
The statement pair and its imported closure remain unchanged.

Set `A = PresentedAffinoidAlgebra.ofStrict K P`,
`e = PresentedAffinoidAlgebra.strictEquiv K P`, and `fRel = e.symm f`.
The proof keeps the actual strict rational quotients for `laurentUpper f`,
`laurentLower f`, and their four-variable `inter`. Its targets remain the
actual relative `BinaryLaurent.Upper`, `Lower`, and two-variable `Overlap`
over `A`.

## The three equivalences

The strict-to-relative constructor `RationalLocalization.relativeEquiv`
is applied to the three original rational data. It bridges
the actual strict scalar closed-ideal quotient to the intrinsic relative
rational quotient, using the published `StrictComparison`,
`RelativeSeriesComparison`, `RelativeEquationComparison`,
`RelativeRationalPresentation`, and `RelativeRationalComparison`
interfaces. This assembly adds no replacement for those quotients and
assumes no comparison theorem as a parameter.

For the upper datum, its denominator is `1` and its only numerator is `f`.
Preservation of one under `e.symm` identifies the transported denominator
with `1`; the numerator becomes `fRel`. Equality transport through
`relativeRationalEquivOfEq` therefore produces `eUpper`. For the lower
datum, the denominator becomes `fRel` and the constant numerator tuple
becomes the constant tuple `1`; the same equality transport produces
`eLower`. Equality transport is bounded in both directions because
eliminating the equalities leaves the identity bounded algebra equivalence.

The original intersection has arity four. Worker 101's
`laurent_inter_denominator` computes its denominator as `f`, and
`laurent_inter_numerator_strictEquiv` computes the transported numerator
tuple, in the actual product order, as
`(fRel, 1, fRel ^ 2, fRel)`. Equality transport thus identifies the output
of the strict-to-relative comparison with `BinaryLaurent.ProductOverlap`.
Composing with the separately constructed
`BinaryLaurent.productOverlapEquiv` gives `eOverlap` in the required
strict-to-relative direction.

The imported overlap construction uses explicit bounded substitutions
`(Z0,Z1,Z2,Z3) -> (1,Y,X,1)` and `(X,Y) -> (Z2,Z1)`. The relation
`fRel * Z1 = 1` yields `Z0 = Z3 = 1` and `Z2 = baseMap(fRel)`, so these
substitutions are inverse. Coordinate bounds and `norm_one <= 1` cover
zero quotients as well. This construction is an independent prerequisite,
not an analytic exactness or gluing argument.

## The five squares

Each coefficient law first applies
`RationalLocalization.relativeEquiv_baseMap`, and then
`relativeRationalEquivOfEq_baseMap`. The overlap law additionally applies
the coefficient law of `productOverlapEquiv`. These are pointwise laws
on every actual element `a : P`, with relative coefficient `e.symm a`.
No coefficient law is supplied as an extra theorem hypothesis.

The three proved coefficient laws are then passed to
`binaryLaurent_left_square` and `binaryLaurent_right_square`. Those
elementary lemmas apply the published strict `RationalData.hom_ext` to
bounded maps out of the upper and lower quotients, reduce to their
coefficient maps, and use `Inclusion.restriction_comp_baseMap` with
`BinaryLaurent.left_upperBase` or `right_lowerBase`. Evaluating their
map equalities at each section gives precisely the two pointwise
restriction squares required by the target. Finally the proof supplies
all three constructed equivalences and all five laws together.

## Original sources and derived provenance

The retained original passages were read directly. Piotr Achinger,
*Introduction to non-Archimedean Geometry* (November 22, 2020), registered
as `achinger-2020-non-archimedean-geometry-nov22`, PDF SHA256
`666cc6a90efbfc05f5fa0156044a259beaabdf989c45b633542e1cd2cdc0ec95`,
printed p.64, Proposition 7.1.1 and the opening of its proof, gives the
relative quotient formulas `A<X>/(X-f)`, `A<Y>/(fY-1)`, and
`A<X,Y>/(X-f,fY-1)`. Printed pp.63 and 65 explain their role in the
analytic exactness theorem. Printed p.6 assumes nontrivial valuation;
the present presentation comparisons use no small-scalar argument.

Vladimir G. Berkovich, *Non-Archimedean analytic spaces*, Trieste lectures
(2009), registered as `berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`,
printed p.8, Definition 2.1.6(i), defines relative restricted series and
the weighted Gauss norm. Exercise 2.2.2(i)-(ii), printed p.9, gives the
Laurent and rational equations; part (iii) states closure under
intersection without supplying this Library's product presentation.
The current literature index and project/public errata notes were
searched; no applicable registered errata note was found for either
retained edition.

Neither source states the concrete equivalences between this Library's
actual strict and relative quotient carriers, or its four-to-two-variable
overlap substitution. These are derived presentation comparisons built
from the named Library interfaces. This assembly uses only their
constructed equivalences and proved coefficient formulas.

All radii here are one, and the statement concerns scalar algebras and
maps. Trivial scalar valuations, zero algebras, nilpotent `f`, and empty
loci remain in scope. This proof establishes only the published
diagram comparison, with no exactness, gluing, descent, higher Cech
exactness, admissibility, arbitrary-radius comparison, or finite-module
conclusion. The strict binary gluing and its relative and whole-spectrum
parents retain their separate targets.
