# Subgroup functors of group schemes over an arbitrary base

This module defines subgroup functors of a group scheme over any base scheme. Dynamic subgroups
and other subgroup constructions in later modules are stated in this language.

## Source and provenance

Conrad, *Reductive group schemes* (2014), Theorem 4.1.7 (PDF pp. 112–113), describes
`P_G(λ)`, `U_G(λ)` and `Z_G(λ)` as subfunctors of `G` and says that "the three subfunctors of `G`
under consideration are subgroup functors". He then asks whether such a subfunctor is
represented by a closed subgroup scheme. This module records that notion for the Library's
general-base group schemes `GroupScheme S`, which are group objects in `Over S`. Conrad's
functors are defined on `k`-algebras over an affine base `Spec k`. Here the test objects are all
schemes `T` over `S`, so non-affine and non-reduced tests are included. The structure has no
sheaf condition: it is a presheaf of subgroups of the functor of points of `G`. The definitions
below are the standard internal ones. Apart from the subgroup-functor notion itself, they make no
claim to follow a particular source.

## Definitions

Fix a scheme `S` and a group scheme `G` over `S`. For every `T` over `S`, the set of
`T`-points `T ⟶ G.X` in `Over S` is a group, with the group law that the group object induces.

- `SubgroupFunctor G` is a structure with two fields:
  - `carrier T : Subgroup (T ⟶ G.X)`, a subgroup of `T`-points for every `T : Over S`;
  - `comp_mem`: for every morphism `a : T' ⟶ T` over `S` and every `x` in `carrier T`, the
    restriction `a ≫ x` lies in `carrier T'`.
- `SubgroupFunctor.ext`: two subgroup functors with the same subgroups on every test scheme are
  equal.
- The `PartialOrder` instance is pointwise inclusion on every test scheme (`le_def`).
- `F ⊓ F'` is the pointwise intersection (`inf_carrier`). `⊤` is the subgroup functor of all
  points (`top_carrier`). `⊥` is the subgroup functor of identity points (`bot_carrier`). Its
  restriction property uses that the identity point pulls back to the identity point.
- `range f`: for a group-scheme homomorphism `f : H ⟶ G`, the subgroup functor whose
  `T`-points are the points of `G` that factor through `f`. That is, it is the image of the
  homomorphism of point groups induced by `f`. `mem_range` restates membership as the existence of
  `y : T ⟶ H.X` with `y ≫ f = x`.
- `IsRepresentedBy F f`: `f : H ⟶ G` is a monomorphism of schemes over `S` and `range f = F`.
  So `H(T)` maps bijectively onto `F(T)` for every `T`. This is representability of `F` by a
  subgroup scheme mapping monomorphically to `G`. It is **not** required that `f` be a closed
  immersion. Conrad's closedness, finite presentation and other properties of representing
  subgroups are separate properties to be stated separately.
- `IsNormalizedBy F F'`: on every test scheme `T`, conjugation `x ↦ g x g⁻¹` by any point `g`
  of `F'` maps points of `F` to points of `F`. For example, Conrad's Theorem 4.1.7(1) asserts that
  `U_G(λ)` is normalized by `Z_G(λ)`.
- `IsNormal F`: `F` is normalized by `⊤`, so every `F(T)` is a normal subgroup of `G(T)`.

## Base change

Let `b : S' ⟶ S` be a morphism of schemes and let `G_{S'}` be the Library base change
`(GroupScheme.baseChange b).obj G`. For a test scheme `T'` over `S'`, write `T'_S` for `T'`
regarded over `S` via `b` (`(Over.map b).obj T'`). The Library equivalence
`baseChangePointsEquiv b G T'` is a group isomorphism `G_{S'}(T') ≃ G(T'_S)`.

- `SubgroupFunctor.baseChange b F` is the subgroup functor of `G_{S'}` whose `T'`-points are
  the preimages under this isomorphism of the points of `F` over `T'_S`. Restriction stability
  follows from the naturality lemma `baseChangePointsEquiv_naturality`.
- `mem_baseChange` restates membership by definition.

This is the functorial base change of a subfunctor, `F_{S'}(T') = F(T')` for `S'`-schemes
`T'`. Conrad (p. 114) uses this when he notes that the formation of `P_G(λ)`, `U_G(λ)` and
`Z_G(λ)` commutes with base change.
