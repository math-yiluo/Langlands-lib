# Geometric atlas covers from split generic components

This is an internal supporting construction for the geometric component-count
proof. It uses the actual geometric fibres and point topology in
`GeometricFibreComponentsStatement`; it does not alter that statement.

## Residue and geometric fibre comparison

`geometricAtlasResidueFiberIso U p` identifies the residue fibre of the chart
structure map, followed by base change to the algebraic closure of the residue
field, with the scheme underlying the product chart at the canonical geometric
point. The construction composes the pullback-pasting isomorphism with the
inverse of `Over.prodLeftIsoPullback`. Its first-projection equation is proved
explicitly.

For an arbitrary family of morphisms into the chart, pulling back
`geometricAtlasCoverSets` along this isomorphism gives exactly the ranges of the
base changes of their residue-fibre pieces. No closedness or finiteness is
needed for this set identity. The existing theorem
`isConnected_fieldBaseChangeSubschemeRanges` then shows that a geometrically
connected residue-fibre piece gives a nonempty connected geometric atlas cover
member. Similarly, the residue-fibre cover property gives coverage of the
geometric atlas fibre after the field extension.

## Constancy for a split generic atlas

`exists_open_geometricComponentsEquiv_of_split_generic` assumes a Noetherian
scheme base, a quasi-separated algebraic space, a surjective etale scheme
chart whose structure map is locally of finite type and quasi-compact, a point
generic for the whole base, and
`FiberComponentsGeometricallyIrreducible U.hom η`. This last hypothesis asserts
geometric irreducibility of the reduced induced schemes of every actual
irreducible component of the generic chart fibre.

The generic fibre is Noetherian, so its irreducible-component label set is
finite. The published geometric-irreducibility spreading theorem and
`exists_open_genericComponentClosures_geometricallyIrreducible_and_incidence`
give a neighbourhood where the closures of these components cover every
residue fibre and their pieces are geometrically irreducible. Geometric
irreducibility implies geometric connectedness. The comparison above therefore
supplies connected geometric atlas covers throughout that neighbourhood.

Independently, constructibility of the finitely many closed-cover kernel-pair
overlap images gives a neighbourhood where their entire membership pattern is
constant. On the intersection, `geometricAtlasClosedCoverComponentsEquiv`
computes each fibre's actual connected components by the quotient of the same
finite label set. `Quot.congr` identifies these quotients with the one at the
generic point. This proves existence of an equivalence of actual component sets
for every point of that open neighbourhood, with the Library point topology
specified explicitly.

`exists_open_geometricFibreComponentCount_of_split_generic` specializes to the
spectrum of a Noetherian ring and takes `ENat.card` of these equivalences. Its
conclusion is local constancy of the exact count used in the host statement.
Empty generic fibres and empty component label sets are allowed.

## Provenance and scope

This unit is derived internally from the cited Library constructions and
proved spreading and incidence results; it is not a transcription of an
external source. It retains the split-generic hypothesis. Existence of a finite
splitting base change, descent of component counts from that base, Noetherian
induction, and approximation for arbitrary rings are not proved here. Thus this
unit does not prove the unrestricted constructibility target.
