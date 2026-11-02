# Spatial maps on equivariant stalk families

Author: Worker 13.

This internal construction supplies the actual degree-zero spatial comparison
for the existing ordinary-topological equivariant Godement functor. It uses
the complete direct-image sheaf, every group-labelled restriction, and the
neighborhood-colimit maps of Mathlib stalks.

The commutative ring, spaces and module carriers have universe `u`. The group
has independent universe `v`. Each group operator is continuous. The spatial
map `f : C(X,Y)` is continuous and equivariant. No topology on the group or
coefficients, joint continuity, properness, separation, local compactness,
smoothness or finite-dimensionality is assumed.

For a transport presheaf `F` on `X`, `stalkMap f hf F x` is Mathlib's actual
`stalkPushforward`, from the stalk of `f_*F` at `f(x)` to the stalk of `F`
at `x`. It is induced by inverse images of open neighborhoods.
`germ_stalkMap` computes it on the original germ of every section over an
open in `Y`. Both stalks here belong to the original ordinary presheaves
obtained by forgetting the group labels.

`stalkMap_transport` proves that this map commutes with every group
transport. For `g x = y`, transport from the stalk at `f(y)` to that at
`f(x)`, followed by the spatial stalk map at `x`, equals the spatial map
at `y` followed by the original transport from `F_y` to `F_x`.
The proof tests both maps on germs, uses the original labelled inverse-open
arrow, and applies `germ_stalkPull_arrow`; equivariance supplies its point
identity. `stalkMap_naturality` similarly tests germs to prove compatibility
with every morphism of transport presheaves. `stalkMap_id` is the identity
map, and `stalkMap_comp` is exactly the composite of the two original
spatial stalk maps, using Mathlib's stalk-pushforward composition theorem.
`stalkMap_transport_section` is a pointwise formulation allowing the two
equal expressions `g f(x)` and `f(g x)` in dependent stalk families.

Writing `T_X` for `zeroFunctor R G X`, `zeroMap f hf F` is the actual sheaf
map

```text
T_Y(f_*F) -> f_*(T_X F).
```

Over an open `U` of `Y`, it sends an arbitrary family `s` to the family on
`f^-1(U)` whose value at `x` is `stalkMap f hf F.obj x (s(f(x)))`.
`zeroMap_apply` gives this formula exactly. Linearity follows from the
module stalk maps, and naturality for every labelled open arrow is proved
by `stalkMap_transport_section`. Thus this is a morphism in the full
equivariant sheaf category, with its intrinsic conditions proved.
`zeroNatTrans` packages these maps into a natural transformation
`f_* ⋙ T_Y -> T_X ⋙ f_*`; its naturality is the proved stalk naturality.

`coaugmentation_zeroMap` states that the genuine germ-family map on `f_*F`
followed by `zeroMap` is the direct image of the genuine germ-family map
on `F`. The proof is the original-section germ formula.
`zeroMap_id` and `zeroMap_comp` give identity and spatial composition as
equalities of full sheaf maps. Direct image along the identity and a
composite has the definitionally equal endpoints supplied by `DirectImage`.
Their proofs apply the corresponding stalk equations at every point.

The provenance is internal: combine the existing full `DirectImage` functor,
`Godement.Stalks`, and `Godement.Zero` with Mathlib
`Topology.Sheaves.Stalks`. The construction does not use an assumed spatial
comparison map or assume right exactness of direct image. The dependency
versions are Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

This unit concerns the ordinary-open equivariant sheaf of arbitrary stalk
families. It does not construct spatial maps in higher Godement degrees,
prove acyclicity, identify this construction with derived compact
cohomology or the equivariant-topos Godement resolution, or assert
smoothness of arbitrary stalk families. Those constructions and comparisons,
the analytic equivariant etale realization, arithmetic towers and the
Harris specialization remain separate obligations.
