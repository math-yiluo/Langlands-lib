# Actual free-module maps from section images and matrices

This internal prerequisite for the relative radical filtration constructs actual free-module sheaf maps with prescribed global
section images and proves their action on the canonical pulled-back section
bases on every scheme test. Rectangular global-section matrices define such
actual sheaf maps. This is intended to convert the proved original quotient
transition matrices into the actual linear module maps needed for descent.

`homOfSections` uses the free sheaf's actual universal property and the
compatible restriction family of each prescribed global section. Its original
generator images are verified. Canonical section pullback and its naturality
then give `homOfSections_basis` and the formula for arbitrary pulled-back free
section coordinates.

`homOfMatrix` assigns to each original generator the corresponding column of
the matrix in the actual target free sheaf. `homOfMatrix_coordinates` proves
that its actual module pullback acts by the pulled-back coefficient matrix on
every scheme test. The original global generators detect equality of actual
sheaf maps. This proves the matrix composition and identity rules, and inverse
rectangular matrices give `isoOfMatrices`, an actual sheaf isomorphism.

Over `Spec R`, `vectorGroup_matrixHom_sections` identifies the action of the
original polynomial vector-group matrix homomorphism with the actual
module-sheaf matrix map in the same free-vector section coordinates. The
coefficient conversion is the actual inverse global-sections comparison
`Scheme.ΓSpecIso`; the result is on every scheme test.

There is no constant-rank restriction between source and target, and zero
ranks and empty bases are included. The later transition matrices, their
inverse relations, overlap gluing and descent cocycle still have to be
constructed from the actual quotient comparisons.

Provenance: an internal derivation from the actual free-sheaf universal
property, canonical section pullback, finite-basis coordinate formulas and the
original polynomial vector-group matrix-coordinate formula.
