# Linear torus-centralizer action on actual root vector coordinates

Author: Worker 1045.

This internal module applies the linearity criterion of
`Langlands.GroupScheme.Rational.VectorActionWeightCommuting` to actual relative
root subgroups. For a relative root `a` without higher positive integral
multiples, it constructs actual vector coordinates on a representative of the
intrinsic root subgroup on which the split torus acts through `a`, and shows
that every group mapping into the torus centralizer acts on that representative
by conjugation, scalar linearly in these coordinates over every test scheme, in
every characteristic. All statements hold at an arbitrary universe `u`.

This is the scheme-level linearity input for the action of the whole
centralizer `Z = Z_G(S)` on a root group `U_a`. Rational torus equivariance
alone need not give it: for example, when the characteristic `p` is positive,
`k` is imperfect and `a = p • b`, equivariance under `S(k)` only forces
additivity and linearity over the subfield of `p`-th powers.

## Setting

Let `k` be a field, `S` a commutative group scheme, and `G`, `K` group schemes
over `Spec k`, with `i : S.toGrp ⟶ G`, `a : characterLattice S` and
`z : K ⟶ G`. The published notions used are: the intrinsic root subgroup
functor `RelativeRoot.subgroup i a`, the set `relativeRoots i`,
`RelativeRoot.HasNoHigherRoots i a` (no `n • a` with `2 ≤ n` is a relative
root), the torus-centralizer subgroup functor `torusCentralizer i`, and the
image subgroup functor `SubgroupFunctor.range z`.

## Declarations

In namespace `Langlands.Geometry.Building`:

- `CentralizerLinearRootVectorCoordinates i a z` (structure) consists of
  - a group scheme `rootGroup` with `inclusion : rootGroup ⟶ G` and
    `represented : (RelativeRoot.subgroup i a).IsRepresentedBy inclusion`;
  - a positive natural number `dimension` and vector coordinates
    `coordinates T : (T ⟶ rootGroup.X) ≃* Multiplicative (Fin dimension → Γ(T.left, ⊤))`
    for every test scheme `T` over `Spec k`;
  - an action `torusAction : AutomorphicAction S.toGrp rootGroup` whose image in
    `G` is conjugation by `i` (`torusAction_comp`), for which the coordinates
    are weight coordinates of weight `a`
    (`weight : RelativeRoot.IsWeightVectorCoordinates torusAction a coordinates`);
  - an action `centralizerAction : AutomorphicAction K rootGroup` whose image
    in `G` is conjugation by `z` (`centralizerAction_comp`), and
    `linear : RelativeRoot.IsLinearVectorCoordinates centralizerAction coordinates`.

  The two `_comp` fields say, for every test scheme `T` and points
  `s : T ⟶ S.X`, `q : T ⟶ K.X`, `v : T ⟶ rootGroup.X`, that
  `torusAction.act s v ≫ inclusion = i(s) · v · i(s)⁻¹` and
  `centralizerAction.act q v ≫ inclusion = z(q) · v · z(q)⁻¹`.
- `nonempty_centralizerLinearRootVectorCoordinates_of_noHigherRoots hS i ha hhigh z hz`
  (needs `IsAffineHom G.X.hom`, `Smooth G.X.hom` and `IsAffineHom K.X.hom`):
  for `hS : IsSplitTorus S.toGrp`, `ha : a ∈ relativeRoots i`,
  `hhigh : RelativeRoot.HasNoHigherRoots i a` and
  `hz : SubgroupFunctor.range z ≤ torusCentralizer i`, the type
  `CentralizerLinearRootVectorCoordinates i a z` is nonempty.

Taking `z` to be a representative of the torus centralizer gives the action of
the whole centralizer. The rational consequences (a `k`-linear automorphism of
`k ^ dimension` for each rational point of `K`) follow from the published
`IsLinearVectorCoordinates.actionLinearEquiv` and
`IsLinearVectorCoordinates.vectorAffineCoordinates_smul`.

## Proof

1. The published `RelativeRoot.subgroup_isSmoothConnectedClosed_of_ne_zero`
   (with `a ≠ 0` from `ha`) gives a representative `j : H ⟶ G` of the root
   subgroup. With `b` the conjugation action of `S` on `G`, the published
   `cyclicRootFunctorComparison` identifies the first cyclic weight filtration
   step `weightFiltration b a 1` with the root subgroup, and
   `weightFiltration_two_eq_bot_of_noHigherRoots` makes the second step trivial.
2. The published `cyclicWeightFiltration` at step `1` gives an fppf quotient
   `q : H ⟶ V` by the second step, an `S`-action `c` on `V` with weight
   coordinates `ec` of weight `1 • a = a`, and an `S`-action `d` on `H`
   compatible with `j` and `q`. Since the second step is trivial, `q` is an
   isomorphism `Q = IsFppfQuotient.isoOfBot` (after
   `SubgroupFunctor.comap_bot_of_mono`).
3. The coordinates on `H` are `e = vectorCoordinatesOfIso Q.symm ec`. They are
   natural by `IsNaturalVectorCoordinates.of_iso`, and weight-`a` for `d`
   because `q` intertwines `d` and `c`. The image of `d` in `G` is conjugation
   by `i` (`AutomorphicAction.conjugation_act`).
4. The published `rootActionOfTorusCentralizer` (with ambient `𝟙 G`, the
   hypothesis `range_id_isNormalizedBy z`, and `hz` rewritten through
   `conjugation_fixedSubgroup_eq_torusCentralizer`) gives the action `bZ` of
   `K` on `H` whose image in `G` is conjugation by `z`.
5. `bZ` and `d` commute: after composing with the monomorphism `j`, both sides
   are conjugation by `z(y) · i(s)` and `i(s) · z(y)`, which are equal because
   `z(y)` lies in the torus centralizer.
6. The dimension is positive: the published `exists_rootPoint_of_noHigherRoots`
   gives a nonidentity rational point of the root subgroup, whose preimage in
   `H` would be the identity if the coordinates had length `0`.
7. Linearity is `isLinearVectorCoordinates_of_commute` from the general module,
   applied to `hS`, `a ≠ 0`, the weight coordinates of step 3 and the
   commutation of step 5.

## Provenance

Internal and derived from published Library results; the hypotheses are those
of the Lean statement. The root subgroups, cyclic weight filtrations and the
torus-centralizer action are the published Library formalizations; the
linearity of the centralizer action on root groups is the scheme-level form of
the familiar fact that `Z_G(S)` acts linearly on each root group `U_a` for a
nonmultipliable root (in the setting of Borel–Tits), proved here directly from
the Library's interfaces rather than formalized from a specific numbered
literature result.
