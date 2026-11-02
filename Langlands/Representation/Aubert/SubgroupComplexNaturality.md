# Naturality of the actual subgroup complex and its terminal projection

This internal construction extends `SubgroupComplex` to maps induced by
ambient intertwiners. Author: Worker 194.

The generic declarations in `Langlands.Aubert.CutComplex.Diagram`
apply a family of linear coefficient maps on the total product
(`mapTotal`) and each homogeneous degree (`mapDegree`).
`mapTotal_extend` proves compatibility with homogeneous extension.
When the coefficient maps commute with the diagram's transitions,
`mapTotal_step`, `mapTotal_differential` and
`mapDegree_differential` prove that they commute with the existing
signed differential. The proof checks each deletion step with its
exterior sign and then sums over the finite index set. This is a
generic linear construction, rather than a representation-theoretic
assumption about the actual subgroup maps.

The remaining declarations lie in `Langlands.Aubert.SubgroupComplex`.
For every actual ambient intertwiner `f`, `objectMap` uses the already
constructed `SubgroupTransition.termMap` on each actual function space.
`objectMap_natural` proves its transition square by the imported
pointwise naturality theorem; it is not an additional input.
`degreeMap` equips the corresponding homogeneous map with equivariance,
checked coordinatewise. `degreeMap_differential` specializes the
generic chain-map theorem to these actual maps.

`boundary_map_le` proves that the induced degree map preserves the
incoming boundary submodule. In degree zero the boundary is zero; in
positive degrees the chain-map identity gives an explicit preimage in
the target incoming range. `terminalMap` therefore descends the actual
degree map to the actual terminal quotients using `Submodule.mapQ`.
Its equivariance is checked on quotient representatives.
`terminalMap_comp_projection` proves the naturality square with the
canonical terminal projections. All source and target representation
carrier universes remain independent.

This unit supplies maps and the actual chain and projection squares.
It makes no assertion of exactness, finite-length preservation,
cuspidal support, or irreducibility. The subgroup family still requires
its separate realization by the shared standard-parabolic framework
and its comparison with actual normalized induction and Jacquet
restriction before it becomes the corrected general Aubert complex.
The provenance is the existing explicit subgroup maps, signed
differential and quotient universal property. No additional literature
theorem or new axiom is used.
