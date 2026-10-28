# Compact smooth cutoffs in indexed-family sheaves

Author: Worker 865.

This module is derived supporting infrastructure for the proof of
`Langlands.Cohomology.SmoothGodementZeroCSoftStatement`. Its coordinate hypothesis
is explicit; it does not identify any sheaf with the published coinduction.
It uses the published modules `Langlands.Sheaf.CompactSoft` and
`Langlands.Sheaf.Equivariant.SmoothPart` and Mathlib's compact-neighbourhood and
finite-subcover results. The construction and proofs below are internal
consequences of those formal interfaces, rather than translations of a further
literature statement.

All carriers `R`, `G`, and `X` belong to a common arbitrary universe `u`.
The coefficient ring is commutative. The group is topological, its individual
translations of `X` are continuous, and `HasStableNeighbourhoods G X` holds.
The neighbourhood lemma and the final c-softness theorem additionally assume
that `X` is Hausdorff and locally compact. There is no paracompactness hypothesis
and no joint continuity hypothesis on the action.

The main coordinate data are a family `A : X → ModuleCat R`, an equivariant
module sheaf `F`, and linear equivalences `read U` from its sections to
`FamilySections A U`. The latter is the Type-indexed family

```
∀ (g : G) (y : {y : X // g • y ∈ U.openSet}), A y.1.
```

The supplied `read_map` hypothesis says that pulling back along a transport
arrow `f : U ⟶ V` changes the group index to `f.label * g` and keeps the
coefficient point `y`. The membership proof is supplied by `f.mapsTo` and
`mul_smul`. In particular, `read_restrict` says that an inclusion simply drops
entries outside the smaller open. `read_invariant` says that the inverse action
arrow of a subgroup element `h` changes the group index to `h⁻¹ * g`.

`familyCutoff A F read V hVU s` is a global section of the ambient sheaf:
it keeps the coordinate of `s` when `g • y ∈ V` and is zero otherwise.
This definition requires only the coordinate linear equivalences, with
`hVU : V ≤ U.openSet`. `read_familyCutoff` computes its coordinates.
`familyCutoff_restrict` proves agreement with `s` on `V`;
`familyCutoff_restrict_zero` proves that its restriction to every open disjoint
from `V` is zero.

`exists_compact_stable_neighbourhood` states that a compact set `K` inside an
open `U` has an open neighbourhood `V` and an open subgroup `H` such that
`K ⊆ V`, `closure V ⊆ U`, `closure V` is compact, and `H` stabilizes `V`.
The proof first takes a relatively compact open neighbourhood inside `U`,
then covers `K` by stable neighbourhoods inside that open. A finite subcover
provides `V`; the finite intersection of the associated open subgroups provides
`H`. The closure inclusions and compactness follow from the initially chosen
neighbourhood.

`familyCutoff_locallyFixed` proves that if `V` is stable under an open subgroup,
then cutting off a section preserves local fixedness at every point where the
original section is locally fixed. Given a local witness on an open `T` with
subgroup `J`, the proof uses `J ⊓ H` on the same open `T`. Stability of `V` under
this subgroup and its inverses preserves the predicate `g • y ∈ V`; the two
coordinate cases reduce respectively to the original fixedness equation and
to equality of zero coordinates. It is not necessary to choose a single
subgroup fixing the original section throughout `V`.

`familyCutoff_smooth` assumes `closure V ⊆ U` and that `s` is locally fixed
at every point of `U`. At points in `U`, the preceding lemma applies. Every
point outside `U` lies in the open complement of `closure V`, where the
cutoff restricts to zero. The published zero-section and restriction lemmas
then give local fixedness there. This also handles boundary points of `V`.

The resulting theorem `isCSoft_smooth_of_family` proves

```
IsCSoft ((toSheaf G X (ModuleCat R)).obj
  ((smoothSubsheafFunctor R).obj F)).
```

For a germ along a compact `K`, `exists_setGerm_eq` supplies a smooth section
`s` on an open `U` containing `K`. The stable-neighbourhood lemma supplies
`V` and `H`. The cutoff is globally smooth by `familyCutoff_smooth`, hence
is a section of the smooth subsheaf. It is zero on the complement of
`closure V`, so its closed germ support is contained in that compact closure.
Its restriction to `V` agrees with `s`, so `setGerm_ext` identifies its germ
along `K` with the given germ. The conclusion uses exactly the Library's
colimit-germ definition of `IsCSoft`.

This result still requires the explicit family coordinates and their transport
formula. Applying it to the smooth Godement construction requires a separate
comparison with the published Kan-extension coinduction, followed by the
published Godement comparison. This module makes no claim to provide either
comparison or the full target theorem.
