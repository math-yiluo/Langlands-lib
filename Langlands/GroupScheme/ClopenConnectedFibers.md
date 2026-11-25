# Clopen subgroups of groups with connected fibres

For every scheme `S`, group schemes `G` and `H` over `S`, and homomorphism
`j : G → H` whose underlying scheme map is an open immersion and a closed
immersion, assume that every actual residue-field fibre of `H` is connected.
`clopenConnectedFibersIso` constructs an isomorphism `G ≅ H` whose forward
map is `j`. No flatness, finite presentation, affineness, smoothness or
commutativity assumption is imposed on either group.

The proof of `isIso_of_clopen_of_connectedFibers` first base changes `j` to
each residue field. Its image is an open and closed subset of the connected
target fibre. It is nonempty because the source group has an identity section
over that field. Thus the image is the entire fibre. The published
`surjective_of_fiber` makes the original map surjective. The original open
immersion is flat and monic, and the closed immersion is quasi-compact, so
Mathlib's `Flat.isIso_of_surjective_of_mono` makes the underlying scheme map
an isomorphism. The published group-scheme reflection lemma makes `j` itself
an isomorphism. `clopenConnectedFibersIso` then applies `asIso`.

This is an internal derivation from base change of group homomorphisms,
connectedness of a nonempty clopen subset, fibrewise surjectivity and
isomorphism reflection. It supplies the connected-fibre surjectivity step
after a diagonalizable subgroup lift in the multiplicative-type fibral
criterion. It asserts no existence of such a lift.

These residue-fibre interfaces reuse `isIso_clopen_subgroup_of_connectedFibres` and `clopenSubgroupIsoOfConnectedFibres` from `Reductive/ConnectedActionInnerReduction`, retaining the same underlying morphism.
