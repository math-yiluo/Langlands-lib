# Weighted rational comparisons over a rational target

Authors: Worker 36 and Worker 135.

This module constructs bounded comparisons between actual positive-radius
rational quotient algebras. It adapts Worker 135's published
`StrictTestDomain/RationalRelativeComparison` argument to the weighted
`PresentedAffinoidAlgebra.RationalChart` construction and its coefficient
pushout. It supplies the relative comparison and compatibility transport
needed to apply whole-spectrum scalar gluing over a rational target.

The coefficient field is complete and ultrametric. Its valuation may be
trivial, the presented algebras may have nilpotents or be zero, and all base
and rational polyradii may be arbitrary positive numbers. No nonempty locus,
positive arity, or nonempty covering hypothesis is imposed.

For an actual chart arrow `h : e → d`, the original bounded restriction goes
from `d.algebra` to `e.algebra`. Pulling e back along `d.baseMap` gives an
actual weighted rational quotient over `d.algebra` and its bounded transport
`pullbackMap d.baseMap e`. `Restriction.relativeInverse` constructs a map in
the reverse direction by `RationalPresentation.BaseChange.pushoutLift`:
the two inputs are the identity on `e.algebra` and `h.restriction`.
They agree on the original coefficient algebra by the arrow's structural
map equation.

The pushout equations identify the inverse after the new structural map
with `h.restriction`, and the inverse after transport with the identity.
`hom_ext_base` exposes the published uniqueness theorem for bounded maps
out of a unit-generated weighted rational quotient. Comparing the two maps
after the structural map of d shows that transport after the old restriction
is the new structural map. Applying the same uniqueness result to the
pulled-back chart proves the other inverse law.
`Restriction.relativeEquiv` packages these constructed maps and laws as a
bounded algebra equivalence; `pullbackMap_injective` follows from it.
Neither an output equivalence nor a converse from locus inclusion to chart
arrows is assumed.

`FamilyCovers.relative` maps a point of `d.algebra` to its image in d's locus,
applies the given cover, and uses `pullback_locus`. Thus the pulled-back charts
cover the entire spectrum of `d.algebra`. This step works for any family
indexed in the field universe, without finiteness.

`intersectionComparison` composes transport for the original all-products
intersection with the restriction associated to the inverse of the published
`pullbackInterIso`. This compares the chosen pullback presentation with the
chosen intersection presentation after pullback. Its structural-map equation
and uniqueness over the original coefficient algebra prove its commutation
with each intersection restriction. Applying this bounded map to an original
overlap equality proves `compatible_pullbackMap`. The index universe for this
last compatibility assertion is independent of the field universe, and no
finiteness is required.

These are derived constructions from the published weighted rational
pushout, uniqueness, base change and intersection results. Their geometric
context is Berkovich, *Non-archimedean analytic spaces*, Trieste lectures
(2009), registered as `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`:
Definition 2.2.1 and Exercise 2.2.2(ii)–(iii), printed/PDF p. 9, describe
affinoid domains, weighted rational quotients and intersections.
The displayed bounded equivalence and transport squares are internal
consequences of the imported constructions. This module does not itself
prove scalar gluing, categorical sheafness, higher Cech exactness or
Banach-module admissibility, and it does not construct analytic atlases or
etale sites.
