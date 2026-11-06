# Apartment transport fixing an entire common facet

This internal construction concerns the original `ValuationBuildingData G`
and its original apartment, quotient, and group action, at every universe.
It uses the supplied apartment axioms, the equality of the apartment stabilizer
with the actual normalizer, and injectivity of the apartment map.

The published singleton sharp-fixer apartment transport is strengthened using
AS4 facet constancy: an apartment containing a point of an apartment facet
can be transported to the base apartment by an element of the sharp fixer of
the entire facet. Antitonicity of sharp fixers proves that this element fixes
every point of the facet image.

For an apartment labelled by `g`, the product of the transporting element
with `g` stabilizes the base apartment and therefore belongs to the actual
normalizer. Its affine action defines `facetApartmentTransition`. Injectivity
of the apartment map shows that this affine map agrees with the coordinate
change at every point of the shared facet. The normalizer isometry theorem
for the root-coordinate metric proves that the transition is an isometry.
Consequently distances of two points in one common facet agree in both charts.

These are derived auxiliary constructions for the compatible apartment metric
argument of Kaletha–Prasad, Section 4.2 (printed pp.168–172, PDF pp.199–203).
The exact proof uses the existing Library quotient transport and AS4
constancy, rather than a separate transitivity premise. The corrected
Proposition 4.2.1 uses the more general two-facet apartment comparison;
this module only establishes the single-facet step. It does not construct
a building distance, retraction, or complete NPC metric on the quotient.
