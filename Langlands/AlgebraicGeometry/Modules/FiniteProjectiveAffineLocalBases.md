# Finite local bases from finite projective affine sections

This internal supporting module treats a quasi-coherent module sheaf on an
arbitrary scheme, in any universe. If its actual section module on every affine
open is finite projective, it has actual finite local bases. Ranks may vary
between charts. There is no noetherian or constant-rank hypothesis.

`DerivedSections.exists_freeNeighborhood_of_finite_projective` first treats an
affine spectrum. The finite projective module of sections is finitely presented.
Its localization at the specified prime is finite free over the local ring.
Choose its finite basis and spread that basis to a principal neighborhood using
Mathlib's finite-presentation localization theorem. The existing
`freeChartOfLocalizedBasis` turns the localized basis into an isomorphism of
the restricted sheaf with an actual finite free sheaf.

`exists_freeNeighborhood_of_finite_projective_affineSections` chooses an
affine neighborhood of the specified point in the original scheme. The
published `FieldGlobalFunctions.affineChartSectionsIso` identifies the sections
after restriction to its spectrum with the original affine sections, with the
same base scalars. Transport finite projectivity across this isomorphism and
apply the affine result. Restriction composition and the open-image chart
comparison give an actual free neighborhood on the original scheme.

`hasFiniteLocalBasis_of_finite_projective_affineSections` chooses one such
neighborhood and basis at each point. The existing free-neighborhood generators
then give a covering family of finite local bases.

The provenance is the existing affine free-chart construction, the canonical
affine chart section comparison, and Mathlib's finite projective module
localization and basis spreading results. This generalizes the existing
constant-rank free-neighborhood argument without asserting any global rank.
