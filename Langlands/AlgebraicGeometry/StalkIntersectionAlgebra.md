# Rational functions regular at a set of points

This internal construction supplies the canonical ring maps for the
semilocal intersection in Bosch–Lütkebohmert–Raynaud, *Néron Models*,
§6.4 Lemma 4. It applies to an integral scheme in every universe.

`stalkIntersection X E` is the intersection, inside `X.functionField`,
of the actual image subrings of the stalks at `E`. Its elements are
precisely the rational functions regular at every selected point.
`stalkIntersectionToStalk` constructs the canonical map to each
selected local ring. The compatibility theorem proves that its
composite with the local ring's inclusion into the function field
is the inclusion of the intersection.

For a morphism `p : X ⟶ Spec R`, `baseToStalk` and
`baseToFunctionField` construct the induced ring maps using full
faithfulness of the spectrum functor. The stalk-specialization equation
proves that they commute with the function-field embeddings.
Consequently `baseToStalkIntersection` maps `R` into the intersection,
and `stalkIntersectionAlgebra` gives its actual `R`-algebra structure.
`stalkIntersection_generic_over` retains the corresponding equation of
scheme morphisms over the base.

The construction allows an arbitrary set `E`: no finiteness, normality
or dimension bound is needed for these maps. The empty intersection is
the whole function field. Removing the generic point leaves the
intersection unchanged. No fraction-field or semilocal localization
property of this intersection is asserted here; those need additional
hypotheses.
