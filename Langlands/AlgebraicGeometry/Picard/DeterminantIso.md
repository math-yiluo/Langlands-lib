# Determinant lines and module-sheaf isomorphisms

This internal derived construction transports actual finite local frame
systems along an isomorphism of module sheaves. The resulting section
bases are the images of the original bases under the induced linear
equivalences on sections. Their transition matrices and determinant
cocycles are unchanged.

`mapFramesIso` identifies the original determinant sheaf with the one
constructed using transported frames and preserves the local generators.
Composing it with the comparison to a target frame system gives `isoMap`,
an actual isomorphism of determinant sheaves even when the source and
target use different covers.

On any open inside a source chart and a target chart, the generator maps
to the target generator multiplied by `isoUnit`, the determinant of the
actual module-sheaf isomorphism in the two actual section bases. Composition
of the coordinate matrices proves multiplication of these units.

`isoMap_refl` and `isoMap_comp` prove identity and composition as equalities
of actual sheaf isomorphisms. The identity proof checks the generator on
each chart. For composition, the three covers give a covering family of
triple intersections. Local scalar generation, linearity and multiplication
of the determinant coefficients prove equality on each intersection, and
sheaf separation proves the global equality.

`lineBundleIsoMap` lifts the resulting isomorphism to the full subcategory
of actual locally free rank-one sheaves. Its identity and composition
laws follow from the sheaf laws. Every frame family uses the same finite
basis index type, but the modules, chart index types and covers may differ.

This construction derives from the actual section-basis equivalence,
Mathlib's free-sheaf naturality and coordinate-matrix composition, and
the determinant cover comparisons and cocycle gluing imported here.
It does not yet supply determinant pullback comparisons, variable rank
assembly, or a parabolic polarization or its ampleness.
