# Connected components of real points

`Langlands.GroupScheme.realPointComponents` proves
`Langlands.GroupScheme.RealPointComponentsStatement`. The real
points of a simply connected semisimple group form a connected space, and
the real points of a connected reductive group have finitely many connected
components. Both conclusions use the evaluation topology. The source
comparison for Milne's *Algebraic Groups* (2017), Theorem 25.54 and
Corollary 25.55, is in the statement's documentation. [Statement](RealPointComponentsStatement.md)

For connectedness, simple connectedness gives connected reductivity. The
proof uses the resulting affineness of the structure morphism as a local
instance when applying the fixed-coroot criterion. The assembly theorem
chooses a maximal real split torus. `realReductiveSplitTorusComponents`
supplies a point of that torus in every real connected component. The
cocharacter norm reduction places all these representatives in the
identity component once the conjugation-fixed simple coroot values at −1
lie there.
`fixedSimpleCorootSignsInIdentity_of_isConnectedReductive` supplies this
condition by expressing those values through descended root-group points
and using their affine-line contractions. It follows that the identity
component contains every real point. [Assembly](RealPointComponentsFixedCorootAssembly.md),
[split-torus representatives](RealReductiveSplitTorusComponentsProof.md),
[fixed simple coroots](RealFixedSimpleCorootSign.md)

For finiteness, the same assembly uses
`finite_connectedComponents_of_isConnectedReductive`. Polar decomposition
puts a representative of every component in a compact subgroup.
Local connectedness makes the space of components discrete, so the
compact image of that subgroup is finite. [Finiteness proof](RealPointComponentsFinite.md)
