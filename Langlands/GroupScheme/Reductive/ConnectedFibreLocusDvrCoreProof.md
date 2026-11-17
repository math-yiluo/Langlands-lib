# Connectedness specializes for smooth affine groups over DVRs

The theorem `Langlands.GroupScheme.ConnectedFibreLocus.dvrCore` proves
`DvrCoreStatement` in every universe.

Let `G` be a smooth affine group over a discrete valuation ring `R`, all of whose
geometric fibre identity components are reductive, and suppose its fibre over
a fraction field `K` is connected. Choose the smooth geometrically connected
relative identity component `H` and its open inclusion `i : H → G` using the
published existence theorem. The published DVR affineness theorem makes `H`
affine. The geometric-fibre comparison in `ConnectedFibreDvrGeometry` then
proves that `H` is reductive.

The generic inclusion is an open immersion and, as a monomorphism of smooth
affine groups over a field, also a closed immersion. Its image is nonempty
because the generic fibre of `H` is geometrically connected. Since the generic
fibre of `G` is connected, the image is the entire generic fibre. Thus the
generic inclusion is an isomorphism.

The published étale DVR open-subgroup isomorphism theorem makes `i` itself an
isomorphism. Its base change to the canonical residue field of `R` is therefore
surjective. The source special fibre is connected by geometric connectedness
of `H`, so its image, the special fibre of `G`, is connected.

This is an internal proof from published results, with no use of the
connected-fibre closed-locus statement being proved.
