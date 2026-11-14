# Algebraic opposite-root rank-one coordinates

This module defines internal algebraic cores of the published
`ValuedSL2RootCoordinates` and `ValuedSU3RootCoordinates` records. It asserts no
existence result. The cores are defined over an arbitrary field `k : Type u`,
without a valuation, topology or apartment. The common parameters are commutative
group schemes `S,Z`, a group scheme `G`, morphisms `i : S.toGrp ⟶ G`,
`j : Z.toGrp ⟶ G`, `s : S.toGrp ⟶ Z.toGrp`, and `b : characterLattice S`.
The definitions require no reductivity, root-membership or centralizer hypotheses.
Those belong to any later existence statement.

`AlgebraicSL2RootCoordinates i j s b` contains a finite separable extension
`E/k`, specified-field positive and negative root coordinates at `b` and `-b`
on that same field, one homomorphism `rho : SL₂(E) → G(k)`, and an actual
group-scheme morphism `coroot : Res_{E/k} Gm → Z.toGrp`. The two coordinate
records retain their own full-`Z` characters, their character restriction
identities and their conjugation identities. For every `t : E`, the image under
`rho` of the upper transvection with entry `t` is the positive coordinate, and
the image of the lower transvection with entry `t` is the negative coordinate.
For every unit `t : Eˣ`, the point of the induced torus corresponding to `t`
under `WeilGm.rationalUnitsEquiv` maps by `coroot` and then `j` to
`rho (diag(t,t⁻¹))`, using `SpecialLinear.Root.contractingMatrix`.

`AlgebraicSU3RootCoordinates i j s b` contains a compatible field tower
`k → E → L`, with both `E/k` and `L/k` finite separable and `L/E` separable
quadratic. The supplied algebra structures have a scalar-tower witness. Its
positive and negative records are `RootUnitaryCoordinatesOn` at `b` and `-b`
on this same tower, retaining each sign's full-`Z` character, restriction and
conjugation identities, and literal double-root identification. Its single
homomorphism `rho` has domain
`SU3Root.specialUnitarySubgroup (SU3Root.fieldInvolution E L)` and codomain
`G(k)`. For every unitary root parameter `p`, it sends the actual upper
`Parameters.embedding p` and `oppositeEmbedding p` to the positive and negative
coordinates. Its actual morphism `coroot : Res_{L/k} Gm → Z.toGrp` maps the
point corresponding to every `t : Lˣ`, followed by `j`, to the image under
`rho` of `SU3Root.diagonal t`.

These cores preserve exactly the field, coordinate, homomorphism and coroot
fields of the published valued records. They include neither a common origin
nor any depth identity, and do not assert that a Weyl element maps to a torus
normalizer. All field and algebra projections needed to use the records are
registered as instances, as for the valued records.

`ValuedSL2RootCoordinates.toAlgebraic` and
`ValuedSU3RootCoordinates.toAlgebraic` discard the common origin and depth
identities, preserving the other fields literally. Their target takes
`Z = B.centralizerTorus hZ`; its underlying group scheme is definitionally the
supplied centralizer. They apply to the original nonarchimedean local-field
building data at arbitrary universe `u`.

## Provenance

This is internal, derived interface design. Each retained field is copied from
`Langlands.Geometry.Building.QuasiSplitValuedRankOneCoordinates`, with the base
field generalized and the torus target supplied as `Z`. The only added
constructions are the two forgetful maps, implemented by copying projections.
The source module's Markdown gives the literature motivation for the original
valued records; this module makes no additional literature claim or mathematical
existence assertion.
