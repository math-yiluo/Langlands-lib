# Existence of a maximal torus over the original field: proof

Worker 1390.

`Langlands.GroupScheme.maximalTorusExistence` proves
`Langlands.GroupScheme.MaximalTorusExistenceStatement.{u}` for every universe `u`.
The statement is in `Langlands.GroupScheme.Torus.ExistenceStatement`, whose
Markdown cites Milne, *Algebraic Groups* (2017), Theorem 17.82 and Corollary 17.83.
The proof does not follow that source. Among the closed subgroups of `G` that become
split tori over some extension field, it picks one whose split rank is as large as
possible. The rank is bounded by the dimension of the Lie kernel of `G`. Larger
closed tori would have larger rank, so the chosen torus is maximal. The proof works
over any field `k`, with no perfectness or characteristic assumption, and does not
use connectedness of `G`. It uses smoothness only to get that `G.X.hom` is locally
of finite type.

Every auxiliary declaration is in the namespace
`Langlands.GroupScheme.TorusExistence`. Throughout, `algebraBaseMap k K` is the
morphism `Spec K ⟶ Spec k` of a field extension (from `Torus.LatticeGalois`), and
`GroupScheme.baseChange (algebraBaseMap k K)` is extension of the field to `K`.

## Base change along a field extension

`isAffineHom_baseChange` and `locallyOfFiniteType_baseChange` say that `G_K` again
has an affine, resp. locally finite type, structure morphism. Both reduce to
stability of these properties under pullback. The file makes them local instances.

## A bound for the ranks of closed tori

The section `Bound` assumes that `G.X.hom` is affine and locally of finite type.

* `finrank_lieKernel_baseChange G K`: the `K`-dimension of the Lie kernel of `G_K`
  at `K` equals the `k`-dimension of the Lie kernel `lieKernel G k` of `G`. Three
  published results give this. `Lie.kernelBaseChangeLinearEquiv k K G K` identifies
  the Lie kernel of `G_K` at `K` with that of `G` at `K`.
  `Lie.kernelScalarExtension G K` identifies `K ⊗[k] lieKernel G k` with the latter.
  `Module.finrank_baseChange` computes the dimension of the tensor product.
* `card_le_finrank G i hi K I e`: let `i : T ⟶ G` be a closed subgroup and let
  `e : T_K ≅ 𝔾_m^I` over a field `K`, with `I` finite. Then
  `Nat.card I ≤ finrank k (lieKernel G k)`. The composite `e.inv ≫ i_K` embeds
  `𝔾_m^I` into `G_K` as a closed subgroup, by `IsClosedSubgroup.baseChange` and
  `IsClosedSubgroup.iso_comp`. The published `splitTorus.card_le_finrank_lieKernel`
  bounds `Nat.card I` by the `K`-dimension of the Lie kernel of `G_K`. The previous
  item rewrites that dimension. Finite-dimensionality comes from the published
  instance `Lie.finiteDimensional_lieKernel`.

## Splittings over larger fields

* `nonempty_splitIso_of_comp b c h T I e`: an isomorphism of the base change of `T`
  along `b : S' ⟶ S` with `𝔾_m^I` over `S'` gives one over any `S''` through
  `c : S'' ⟶ S'` with `c ≫ b = d`, after base change along `d`. It composes the
  pseudofunctoriality isomorphisms of pullback (`Over.pullbackComp`,
  `Functor.mapGrpCompIso`) with `splitTorus.baseChangeIso`.
* `nonempty_splitIso_extension φ hφ T I e` specializes this to fields. Let
  `T_K ≅ 𝔾_m^I`, and let `φ : K →+* E` be compatible with the maps from `k`. Then
  `T_E ≅ 𝔾_m^I` with the same index type.

## Isomorphisms descend along field extensions

* `flat_and_surjective_algebraBaseMap`: `Spec K ⟶ Spec k` is flat and surjective.
  Every vector space is free, so `K` is faithfully flat over `k`. Mathlib's
  `flat_and_surjective_SpecMap_iff` then applies. `flat_algebraBaseMap` and
  `surjective_algebraBaseMap` are the two halves, used as local instances.
* `isIso_of_isIso_baseChange K f`: a homomorphism `f : H ⟶ G` of group schemes over
  `k` is an isomorphism if `f_K` is one. The square
  ```
  H_K --f_K--> G_K
   |            |
   H  ---f--->  G
  ```
  is a pullback. It is proved with the pasting argument from the published
  `IsClosedSubgroup.baseChange` (`Langlands.GroupScheme.SubgroupBaseChange`). Its
  right edge `G_K ⟶ G` is the base change of `Spec K ⟶ Spec k`. It is therefore
  surjective, flat and quasi-compact. Mathlib's instance
  `descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact` (fpqc descent of
  isomorphisms) shows that the underlying scheme morphism of `f` is an isomorphism.
  The forgetful functors `Grp → Mon → Over → Scheme` reflect isomorphisms, so `f` is
  an isomorphism.

## The trivial torus

The section `Trivial` works over an arbitrary base scheme `S`.

* `splitTorusEmptyIso`: the split torus on `PEmpty` is isomorphic to the trivial
  group object `Grp.trivial (Over S)`. Both have exactly one point over every
  `T : Over S`, so the published `isoOfPointModels` applies, with `PUnit` as the
  common point model.
* The imported `Langlands.GroupScheme.kernelUnit_isClosedSubgroup G` from
  [WeightSupportVanishing](../Rational/WeightSupportVanishing.md): the identity section `kernelUnit G` of a group
  scheme with separated structure morphism is a closed subgroup. Its composite with
  `G.X.hom` is the identity, a closed immersion, and `G.X.hom` is separated.
* `trivialTorus k` is `splitTorus.commGroupScheme (Spec k) PEmpty`.
  `isTorus_trivialTorus k` says that it is a torus: it is split.
* `trivialTorusHom G` is `splitTorusEmptyIso.hom ≫ kernelUnit G`.
  `isClosedSubgroup_trivialTorusHom G` says that it is a closed subgroup when
  `G.X.hom` is separated.
* `exists_closedTorus G`: every group scheme over `k` with separated structure
  morphism has a closed torus,
  `∃ (T : CommGroupScheme (Spec k)) (i : T.toGrp ⟶ G), IsTorus T.toGrp ∧
  IsClosedSubgroup i`. The witness is the trivial torus.

## Closed tori of maximal rank

* `IsClosedTorusRank G n` is an auxiliary predicate on `ℕ`, not a mathematical
  definition from the literature. It says that there is a commutative group scheme
  `T` with a closed subgroup `i : T.toGrp ⟶ G`, a field `K` over `k` and a finite
  type `I` with `T_K ≅ 𝔾_m^I` and `Nat.card I = n`.
* `exists_isMaximalTorus G`, for `[Smooth G.X.hom] [IsAffineHom G.X.hom]`, gives a
  commutative group scheme `T` over `k` and `i : T.toGrp ⟶ G` with
  `IsMaximalTorus i`. Let `N = finrank k (lieKernel G k)`. Then:
  1. By `card_le_finrank`, every `n` with `IsClosedTorusRank G n` satisfies `n ≤ N`.
  2. `IsClosedTorusRank G 0` holds for the trivial torus, split over `k` itself by
     `splitTorus.baseChangeIso`.
  3. `Nat.findGreatest_spec` gives `T`, `i`, `K`, `I` and `e : T_K ≅ 𝔾_m^I` with
     `Nat.card I = Nat.findGreatest (IsClosedTorusRank G) N`. Then `T` is a torus,
     witnessed by `K` and `e`, and `i` is a closed subgroup.
  4. For maximality, let `T'` be a torus with closed subgroup `i'`, split as
     `T'_{K'} ≅ 𝔾_m^{I'}`, and let `f : T ⟶ T'` satisfy `f ≫ i' = i`. Then
     `IsClosedTorusRank G (Nat.card I')` holds. By step 1 and `Nat.le_findGreatest`,
     `Nat.card I' ≤ Nat.card I`.
  5. `TorusBaseChange.commonExtension k K K'` gives a field `E` containing `K` and
     `K'` over `k`. By `nonempty_splitIso_extension`, `T_E ≅ 𝔾_m^I` and
     `T'_E ≅ 𝔾_m^{I'}`. Since `i` is a closed immersion, its underlying `Over`
     morphism is a monomorphism. So is the underlying morphism of `f`, as
     `f ≫ i' = i`. Pullback preserves monomorphisms, so `f_E` is one too.
  6. The published `splitTorus.isIso_of_mono_of_iso` makes `f_E` an isomorphism, by
     step 4. `isIso_of_isIso_baseChange` then makes `f` an isomorphism.
* `maximalTorusExistence` applies `exists_isMaximalTorus` to each `k` and `G`.
