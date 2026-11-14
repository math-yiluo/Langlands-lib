# Statement: maximality of a torus in a reductive fibre spreads to a neighbourhood

Worker 75.

`Langlands.GroupScheme.MaximalTorusFibreSpreadingStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.FieldPointMaximality`](FieldPointMaximality.md), and through it the field
  predicate `IsMaximalTorus` of [`Torus.Maximal`](Maximal.md) and the base change
  `CommGroupScheme.baseChange` of commutative group schemes;
- [`Torus.Relative`](Relative.md), which provides `RelativeTorus.IsTorus`;
- [`Rational.TorusCentralizer`](../Rational/TorusCentralizer.md), which provides the
  centralizer subgroup functor `torusCentralizer`;
- [`Reductive.IdentityComponentLocus`](../Reductive/IdentityComponentLocus.md), which
  provides `identityComponentReductiveLocus`;
- [`RelativeIdentityComponent`](../RelativeIdentityComponent.md), which provides
  `IsRelativeIdentityComponent`.

Through these imports it also uses `IsClosedSubgroup` from
[`Reductive.Basic`](../Reductive/Basic.md), `SubgroupFunctor.IsRepresentedBy` from
[`SubgroupFunctor`](../SubgroupFunctor.md), and `GroupScheme` with its base-change
functor `GroupScheme.baseChange` from `Langlands.AbelianScheme.GroupScheme`.
`GroupScheme S` is `Grp (Over S)`, and the underlying morphism of
`(GroupScheme.baseChange f).obj H` is `pullback.snd H.X.hom f`.

It states Conrad's Proposition 3.1.9(2): if a torus `T` in a smooth affine group `G` is
maximal in a fibre `G_s` whose identity component is reductive, then near `s` the torus
`T` is maximal in every fibre and is the identity component of its centralizer.

## Statement and quantifiers

The proposition quantifies over:

- a scheme `S : Scheme.{u}`;
- a group scheme `G : GroupScheme S` with the instances `Smooth G.X.hom` and
  `IsAffineHom G.X.hom`. This is Conrad's smooth `S`-affine group scheme `G → S`;
- a commutative group scheme `T : CommGroupScheme S` and a homomorphism
  `i : T.toGrp ⟶ G`, with proofs of `RelativeTorus.IsTorus T.toGrp` and
  `IsClosedSubgroup i`. `RelativeTorus.IsTorus` says that `T` is a split torus
  (`IsSplitTorus`) on each member of some jointly surjective étale cover of `S`, the rank
  being allowed to vary between members. `IsClosedSubgroup i` says that the underlying
  morphism of schemes of `i` is a closed immersion. This is Conrad's torus `T ⊂ G`;
- a point `s : S` with `s ∈ identityComponentReductiveLocus G`. That set consists of the
  points whose geometric fibre `G_{s̄}` has connected reductive identity component
  (`IsConnectedReductive`). This is Conrad's hypothesis "`G⁰_s` is reductive"; see the
  derivation below;
- a proof that the residue fibre of `i` at `s` is a maximal torus. The residue fibre is
  `(GroupScheme.baseChange (S.fromSpecResidueField s)).map i`, the pullback of `i`
  along `Spec κ(s) ⟶ S`, with source the commutative base change
  `(CommGroupScheme.baseChange (S.fromSpecResidueField s)).obj T`. Over a field,
  `IsMaximalTorus j` says that the source of `j` is a torus (`IsTorus`), that `j` is a
  closed subgroup, and that whenever `j = f ≫ j'` with `j'` a closed torus subgroup, the
  homomorphism `f` is an isomorphism.

## Conclusion

There is an open subset `V : S.Opens` with `s ∈ V` such that both of the following hold.

1. For every point `v : S` with `v ∈ V`, the residue fibre
   `(GroupScheme.baseChange (S.fromSpecResidueField v)).map i` is a maximal torus
   (`IsMaximalTorus`, with source the commutative base change of `T`). This is Conrad's
   "`T_v` is a maximal torus in `G⁰_v` for all `v ∈ V`".
2. For every group scheme `Z : GroupScheme S`, homomorphism `z : Z ⟶ G` and
   homomorphism `j : T.toGrp ⟶ Z` such that `(torusCentralizer i).IsRepresentedBy z`
   and `j ≫ z = i`, the base change of `j` along the open immersion `V.ι` satisfies
   `IsRelativeIdentityComponent ((GroupScheme.baseChange V.ι).obj Z)
   ((GroupScheme.baseChange V.ι).map j)`. This is Conrad's `Z_G(T)⁰_V = T_V`.

Here `(torusCentralizer i).IsRepresentedBy z` says that `z` is a monomorphism whose
subgroup functor of points equals the centralizer functor of `i`: a point `g` of `G` over
an `S`-scheme `U` belongs to it when `g` commutes with every point of `T` after every
refinement `U' ⟶ U`. So `Z` is the centralizer `Z_G(T)`. `IsRelativeIdentityComponent H k`
says that `k` is an open immersion and that a point of `H` over any `S`-scheme factors
through `k` exactly when its image in every residue-field fibre lies in the identity
component of that fibre. So clause 2 says that `T_V`, embedded in `Z_V` by `j`, is the
relative identity component of `Z_V`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the printed page numbers.

- Proposition 3.1.9, p.85: "Let G → S be a smooth S-affine group scheme and suppose G⁰_s
  is reductive for some s ∈ S. [...] 2. If T ⊂ G is a torus such that T_s is maximal in
  G⁰_s for some s ∈ S then there exists an open V around s in S such that
  Z_G(T)⁰_V = T_V and T_v is a maximal torus in G⁰_v for all v ∈ V." Conrad adds: "This
  result is essentially [SGA3, XIX, 2.6] (where it is assumed that each G_s is
  connected). Note that in part (2) we assume T exists."
- The proof of (2), pp.85–86: the centralizer `Z_G(T)` is a smooth closed `S`-subgroup
  by Lemma 2.2.4 (p.64); after Zariski localization `T` and `Z_G(T)` have constant and
  equal fibre dimensions, so `T_ξ = (Z_G(T)_ξ)⁰` for all `ξ`; the map `T → Z_G(T)⁰` is
  then an isomorphism by the fibral isomorphism criterion (Lemma B.3.1), and maximality
  of `T_ξ` in `G⁰_ξ` follows from the connectedness of torus centralizers in smooth
  connected affine groups over algebraically closed fields.

## Derivation from the source

- **Torus subgroup.** Conrad's torus `T ⊂ G` is a subgroup that is a torus over `S`.
  Conrad's tori over a base are fpqc-locally isomorphic to powers of `𝔾_m`; for tori this
  is equivalent to being split étale-locally (SGA 3, X, 4.5), which is
  `RelativeTorus.IsTorus`. A multiplicative-type subgroup of a smooth `S`-affine group
  is closed: after Proposition 3.1.6, p.83, Conrad notes that "by Lemma B.1.3, the
  monomorphism H′ → G_S′ must be a closed immersion". So the inclusion is required to be
  a closed immersion.
- **Reductive identity component.** As in
  [`Reductive.IdentityComponentLocus`](../Reductive/IdentityComponentLocus.md), "`G⁰_s`
  is reductive" means that the identity component of the geometric fibre is connected
  reductive, since reductivity over a field is a geometric condition and identity
  components commute with extension of the ground field.
- **Maximality.** Conrad's fibres `T_s ⊂ G⁰_s` are over the residue field `k(s)`. The
  proposition uses the residue fibres along `S.fromSpecResidueField`, exactly as in
  `IsFibrewiseMaximalTorus` of [`Torus.FieldPointMaximality`](FieldPointMaximality.md).
  A torus over a field is connected, so a torus in `G_s` lies in `G⁰_s`, and maximality
  among tori of `G_s` is the same as maximality among tori of `G⁰_s`.
- **Centralizer.** Conrad's `Z_G(T)` is the closed subgroup representing the centralizer
  functor (Lemma 2.2.4). The proposition does not assert that a representing subgroup
  exists; clause 2 applies to every pair `(Z, z)` with
  `(torusCentralizer i).IsRepresentedBy z`. Any two such pairs are isomorphic over `G`,
  since both are monomorphisms with the same functor of points. Because `T` is
  commutative, `i` factors through `z`, and the factorization `j` is unique since `z` is
  a monomorphism; quantifying over all `j` with `j ≫ z = i` therefore loses nothing.
- **Identity component over `V`.** `Z_G(T)⁰_V = T_V` says that, over `V`, the inclusion
  of `T` into `Z_G(T)` identifies `T` with the open subgroup of `Z_G(T)` whose fibres are
  the identity components of the fibres. This is `IsRelativeIdentityComponent` for the
  base change of `j` along `V.ι`. The residue fibres of the base change to `V` at a point
  of `V` are the residue fibres over `S` at that point, so it does not matter whether the
  identity component is formed before or after restricting to `V`.

## Scope

All objects are in universe `u`. The proposition does not state:

- the existence or smoothness of the centralizer `Z_G(T)` over `S` (Lemma 2.2.4);
- Proposition 3.1.9(1), which is
  `IdentityComponentReductiveLocusOpenStatement` in
  [`Reductive.IdentityComponentLocus`](../Reductive/IdentityComponentLocus.md) for
  reductivity; the semisimple variant is not stated here;
- the existence of a torus `T` lifting a maximal torus of `G⁰_s` étale-locally around
  `s` (Proposition 3.1.6, Corollary 3.2.7);
- the fibral isomorphism criterion (Lemma B.3.1).

## Relation to the Library

- `IdentityComponentReductiveLocusOpenStatement` in
  [`Reductive.IdentityComponentLocus`](../Reductive/IdentityComponentLocus.md) is
  Conrad's Proposition 3.1.9(1) for reductivity. Conrad's proof of (1) uses (2).
- `LocalClosedFibreMaximalPropagationStatement` in
  [`Torus.LocalMaximalPropagation`](LocalMaximalPropagation.md) proves, over a local
  ring and for a split torus in a reductive group scheme, that maximality on the closed
  fibre implies maximality on every residue fibre.
- `RelativeSplitTorusLiftingStatement` in
  [`Torus.RelativeLiftingStatement`](RelativeLiftingStatement.md) is a split-torus
  specialization of Proposition 3.1.6, which supplies tori `T` to which the present
  proposition applies.

This module proves none of these relations.
