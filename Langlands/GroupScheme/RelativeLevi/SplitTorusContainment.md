# Spreading parabolic containment with a specified split torus

This internal composition proves that containment of the actual residue-fibre
ranges of two relative parabolics spreads to a Zariski neighbourhood, provided
they contain the same specified split torus and that torus is maximal on the
distinguished residue fibre. The base scheme and universe are arbitrary.

The theorem `exists_open_range_le_of_two_neighbourhoods` combines an equality
of represented subgroup ranges on one open immersion with containment on a
second open. Their pullback retains the original field-valued point. Canonical
pullback tower comparisons transport both range comparisons to this common
base, and etale-image descent gives an open of the original base.

The theorem `exists_open_range_le_of_commonCocharacter` applies this comparison
to two smooth affine subgroup sources with geometrically connected fibres and
one common ambient cocharacter. It assumes that the cocharacter factors through
both sources, presents the larger residue fibre and contains the smaller
residue fibre. Closedness is required only at the distinguished residue fibre;
the larger inclusion is globally monic. LocalPresentation supplies the first
open, LocalContainment the second, and dynamic representability supplies the
common representative used for the comparison.

The torus lemmas lift a cocharacter through each monic containing subgroup and
compare lattice base change with dynamic cocharacter base change. A specified
split torus extends every field-fibre cocharacter over the original base.
The field classification in FieldLieContainment presents the larger fibre by
a cocharacter of that same torus. This yields two source cocharacters with
one common ambient composite. The original residue containment then gives the
smaller fibre's dynamic containment.

The theorem `exists_open_range_le_of_splitTorus_residueFiber` applies this
construction to relative parabolics of a reductive group. ParabolicSourceGeometry
supplies geometric connectedness of their actual sources; smoothness,
affineness, global monicity and residue closedness come from the relative
parabolic predicate. The definition
`splitTorusParabolicContainmentNeighbourhood` selects an actual open containing
the specified point together with the proved range containment.

All containments are subgroup-functor containments on every test scheme.
This derived prerequisite neither assumes nor proves a Lie containment
hypothesis and does not split a torus which is only etale locally split.
