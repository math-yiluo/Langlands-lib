# Affine matrix coordinates of the quasi-split unitary group

Worker 1225. This internal construction transports the published global-section matrix coordinates back to the original affine test algebra using `Corepresented.affineSectionsAlgEquiv`. It is a derived interface for the rank bound and introduces no new group scheme.

`affineMatrixCoordinates` is a homomorphism from actual affine points over an F-algebra R to invertible two-by-two matrices over E tensor R. It is injective because the original point comparison is an equivalence and the section comparison induces an invertible tensor map. Its naturality theorem follows from the naturality of the original matrix coordinates and the global-sections/spectrum isomorphism.

The transported matrices satisfy the original unitary equation. Consequently their inverse is their conjugate adjoint for the antidiagonal Gram matrix. These claims hold in characteristic two and use the existing involutivity result for quadratic conjugation. No rank bound is claimed in this unit.
