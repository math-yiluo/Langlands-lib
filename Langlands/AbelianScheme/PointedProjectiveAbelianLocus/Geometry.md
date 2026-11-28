# Smooth connected geometry near a point of the abelian-scheme locus

For a proper, flat, locally finitely presented family, the complement of
the smooth locus has closed image. The smooth locus commutes with base
change by `Scheme.Hom.smoothLocus_eq_preimage_of_isPullback`. A test family
that is smooth everywhere therefore lies over the complement of this
closed image.

For a smooth proper pointed family the union of the fibre components
through the section is open by `SectionComponent.flatFinitePresentationOpenness`
(EGA IV, 15.6.5). Remove the closed image of its complement. A field-valued
test with connected pullback lies over the resulting open because the
pullback projects surjectively onto the corresponding residue fibre.
Every residue fibre over the open is connected and has a rational point
from the section, hence is geometrically connected.

In the locally noetherian base, the connected component of the test
point in this open is itself open. Over that component the total space
is connected by smooth openness and geometric connectedness.
`smoothConnectedRelativeDimension` gives a constant relative dimension.
Comparison of the topological Krull dimension of the nonempty test fibre
identifies this number with `g`. An affine neighbourhood in the component
gives the required noetherian chart.
