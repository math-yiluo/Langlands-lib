# Closed monomorphisms from split tori over an arbitrary base

For every scheme `S : Scheme.{u}`, split torus `T` over `S`, and affine
`S`-group `G` locally of finite type, `IsSplitTorus.isClosedSubgroup_of_mono`
proves that every homomorphism `f : T ⟶ G` monomorphic on schemes over `S`
is a closed immersion of schemes. There is no Noetherian, smooth-target,
global-affine-base or finite-presentation hypothesis. The split torus has
finite rank by the definition of `IsSplitTorus`.

`SplitTorusMonomorphism.exists_closed_neighbourhood` produces, for each
base point, an actual open immersion through whose base change `f` is
closed. `closedImmersionCover` assembles these into an actual base open
cover, and `isClosedSubgroup_baseChange_cover` records closedness on every
member. Pulling that cover back along the target structure morphism and
using the canonical cartesian base-change square proves the global result.

The fibre argument uses the split torus's smoothness, connectedness and
affineness and `HomImage.isClosedSubgroup_of_mono`, the published field
result for a smooth connected affine source. Monicity is preserved by base
change. The published `exists_open_isClosedImmersion_baseChange` then
extends closedness of the residue-field map to an open neighbourhood of
the base point, retaining its precise residue-point factorization.

This is an internal derivation from the named published interfaces and
Zariski locality of closed immersion. It asserts no separate translation
of external literature. It treats split tori only, and does not claim the
statement for arbitrary groups of multiplicative type or the reductive
closed-immersion theorem.
