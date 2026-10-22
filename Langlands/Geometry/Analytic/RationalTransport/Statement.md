# Bounded transport target for rational presentations

Author: Worker 36.

`RationalPresentation.TransportStatement` concerns the actual closed-ideal
quotients from `RationalPresentation.Definitions`. The coefficient field is
complete and ultrametric; its valuation may be trivial. The two base
presentations may have different arities and arbitrary relation sets. The
numerator tuples have the same finite length, including length zero. Zero
quotients are allowed.

The first clause starts with a bounded base algebra map carrying the actual
quotient images of the denominator and numerators to their specified target
images. It asserts a unique bounded map between the rational quotients that
commutes with the base maps and sends each new source coordinate to the
corresponding new target coordinate. Uniqueness includes both requirements;
agreement on the base alone is not asserted here.

The second clause starts with a bounded base algebra equivalence satisfying
the same compatibility. It asserts a bounded equivalence of the rational
quotients, with positive bounds in both directions, the same base and
coordinate formulas, and commutation of the induced spectrum homeomorphisms
with the base spectrum maps. The spectrum homeomorphism is the actual
contravariant pullback from `BoundedEquivalence.Definitions`.

Neither clause assumes that the denominator and numerators generate the
unit ideal, or that the rational locus is a domain. These are assertions
about the constructed quotient algebras. In particular, the identity base
equivalence compares any two choices of Tate-series representatives of the
same denominator and numerator elements. The statement supplies no
canonical norm bound, equality of quotient norms, arbitrary-radius
construction, or full analytic-domain factorization property.

This is derived implementation infrastructure. Berkovich's *Non-Archimedean
analytic spaces* (Trieste 2009), Definition 2.1.11, printed/PDF p.8, uses
bounded algebra homomorphisms for the opposite category of affinoid spaces.
Exercise 2.2.2(ii), p.9, defines rational quotients from elements of the base
algebra. The present target makes transport and independence from their
chosen Tate-series lifts explicit for the enlarged Tate presentation with
closed generated relation ideal. It does not identify that presentation
with the source's relative-series quotient, replace unit radii by general
radii, or assert Definition 2.2.1's factorization from spectrum containment.
The construction route is convergent evaluation at the target coordinates;
those coordinates have bounded monomials because the target quotient map
is bounded. Inverse base maps then give inverse quotient maps by agreement
on the base and new coordinates.

Registered original: `berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
