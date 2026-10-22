# Explicit terminal object and pullbacks of rational inclusions

Author: Worker 36.

Fix a complete ultrametric normed field K and a presented strict affinoid P.
The category is the published inclusion category on chosen `RationalData K P`.
`generatesUnitIdeal` converts its no-common-spectrum-zero field into the
algebraic unit-ideal condition using the existing equivalence.

`whole` uses denominator one and an empty numerator tuple. Its no-common-zero
condition follows from the value of one under every multiplicative seminorm,
and its locus is the whole spectrum because there are no inequalities.
`toWhole` is the resulting inclusion. `wholeIsTerminal` proves terminality
by this existence and the subsingleton property of all hom sets. This
terminality is in the category of rational inclusions over the fixed base P.

`inter d e` uses the product of the denominators and every pairwise product
of the denominator-extended numerator tuples. The intersection construction's
unit-ideal theorem gives admissibility, then the no-common-zero equivalence
packages these elements as actual rational input. Its quotient algebra is
definitionally the product quotient of `RationalIntersection`.
`locus_inter` invokes the intersection theorem to identify the locus with
the set intersection.

The projections `interLeft` and `interRight` use the two subset inclusions.
`interLift` constructs a map from simultaneous inclusions into d and e.
For any arrows d → t and e → t, `pullbackCone` uses this explicit intersection.
Its square commutes because the hom sets are subsingletons.
`pullbackConeIsLimit` supplies `interLift` as the lift of every cone; the
factorization and uniqueness laws follow from the same subsingleton property.
The object of the cone is thus constructed from the original algebra elements,
not supplied as an assumed pullback.

Finally, `interLeft_restriction` and `interRight_restriction` identify the
bounded algebra maps induced by these inclusions with the separately
constructed `RationalIntersection.leftMap` and `rightMap`. Their equations
over P and uniqueness of the published rational restriction maps prove these
equalities. The directions are contravariant: each map goes from a factor
quotient algebra to the intersection quotient algebra.

This construction retains chosen presentations rather than quotienting them
by equality of loci. All radii are one. Empty numerator tuples, empty loci,
zero or nonreduced quotients and trivial scalar valuations are allowed.
The categorical limit assertions concern rational inclusions over P;
they do not assert preservation of these limits in the ambient category
of all affinoid spaces. The module constructs no covering, structure sheaf,
general affinoid atlas or analytic etale site.

The provenance is derived from Berkovich, *Non-archimedean analytic spaces*,
Trieste lectures (2009), printed/PDF p. 8 Definition 2.1.11 and p. 9
Definition 2.2.1 and Exercise 2.2.2(ii)–(iii), registered as
`berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
These passages give the opposite bounded-algebra direction, the domain
universal property, rational data and closure under intersections.
The named terminal object and pullback cones in the category of chosen data
are derived categorical packaging, not separately named source constructions.
The existing representation theorem tests presented strict affinoids only;
this module does not extend it to the source's unrestricted test class.

The shared `RationalData.generatesUnitIdeal` lemma is imported from
[`RationalRepresentationProof`](RationalRepresentationProof.md).
