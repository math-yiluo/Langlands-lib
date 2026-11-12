# Fibrewise ampleness over a noetherian affine base

Author: Worker 833.

`Langlands.AlgebraicGeometry.Picard.properAffineFibrewiseAmple` proves
exactly `ProperAffineFibrewiseAmpleStatement.{u}` in an arbitrary universe.
For a proper morphism to a locally noetherian affine base and a specified
line bundle ample on every residue-field fibre, it proves absolute
ampleness of this same total bundle.

The proof applies
`LineBundle.isAmple_of_fibrewise_over_affine` from
`AffineBaseAmpleLocality`. That theorem uses the published
`properFibreAmpleSpreading` to obtain ampleness over neighbourhoods of
all base points and globalizes the resulting local sections.

The supporting principal-neighbourhood proof converts a section of a
positive tensor power on a principal open to an ordinary section of the
original tensor power restricted to that open. The published
`PrincipalSectionExtension.exists_global` clears its denominator.
Multiplication by one further copy of the principal function forces the
global generation open to lie in that principal open. There the
function and its denominator power are units, so the resulting whole
generation open is the image of the original affine generation open.
This gives the global section required by the Library's definition of
ampleness at the chosen point.

For neighbourhoods pulled back from an affine base, refinement to a
basic open gives precisely these principal opens on the total scheme.
The inclusion into the original neighbourhood is affine, so the
published affine-pullback ampleness theorem applies. Properness over the
affine base supplies compactness and quasi-separatedness.

All points and actual residue-field fibres are retained. This internal
argument uses the published section and pullback infrastructure. It
does not construct a bundle or establish specialization of ampleness
from the generic fibre.
