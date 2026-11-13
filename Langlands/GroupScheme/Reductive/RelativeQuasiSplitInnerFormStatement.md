# Statement: quasi-split inner forms of reductive group schemes over any base

Worker 75.

`Langlands.GroupScheme.RelativeQuasiSplitInnerFormExistenceStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- Mathlib's `Mathlib.AlgebraicGeometry.Morphisms.Etale`, for `Etale`;
- [`AutomorphicAction`](../AutomorphicAction.md), for `AutomorphicAction`,
  `AutomorphicAction.restrict` and `AutomorphicAction.conjugation`;
- [`Rational.Characters`](../Rational/Characters.md), for the centre `center G`;
- [`Rational.InnerDiscrepancy`](../Rational/InnerDiscrepancy.md), for
  `LocalGroupIso.HasInnerDiscrepancy`, and transitively
  [`LocalGroupIso`](../LocalGroupIso.md), for `LocalGroupIso`;
- [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md),
  for `RelativeRoot.IsFppfQuotient`;
- [`RelativeLevi.Borel`](../RelativeLevi/Borel.md), for `IsRelativeBorelSubgroup` and
  `IsRelativeQuasiSplit`, and transitively [`Reductive.Basic`](Basic.md), for
  `IsReductive` and `IsClosedSubgroup`;
- [`Torus.FieldPointMaximality`](../Torus/FieldPointMaximality.md), for
  `IsFibrewiseMaximalTorus`, and [`Torus.Relative`](../Torus/Relative.md), for
  `RelativeTorus.IsTorus`.

`GroupScheme S` is `Grp (Over S)`, and `CommGroupScheme S` is its commutative version with
underlying group scheme `T.toGrp`.

## Predicates and constructions used

- `IsReductive G`: the structure morphism of `G` is smooth and affine, and every geometric
  fibre of `G` is a connected reductive group over an algebraically closed field.
- `center G`: the subgroup functor of all-test central points of `G`, the functor of points
  of the scheme-theoretic centre `Z_G`.
- `RelativeRoot.IsFppfQuotient N q`: the underlying morphism of `q` is flat, surjective and
  locally of finite presentation, and the range of the scheme kernel of `q` is `N`.
- `AutomorphicAction A G`: an action of `A` on `G` by group automorphisms, given by one
  morphism `A × G → G` with the action laws on the points over every `T : Over S`.
  `c.restrict p` is the action through `p`, and `AutomorphicAction.conjugation (𝟙 G)` is
  conjugation `g · x = g x g⁻¹` of `G` on itself.
- `LocalGroupIso G G' U`, for `U : Over S`: for every `Z : Over S` and every point
  `b : Z ⟶ U`, a group isomorphism `e_b` from the `Z`-points of `G` to the `Z`-points of
  `G'`, natural in `Z`. This is an isomorphism `G_U ≅ G'_U` of group schemes over `U`.
- `e.HasInnerDiscrepancy c`: for every `T : Over S` and every two points
  `b b' : T ⟶ U` there is a point `x : T ⟶ Gad` such that, on every `t : W ⟶ T` and every
  `W`-point `g` of `G`, `e_{t ≫ b} (c.act (t ≫ x) g) = e_{t ≫ b'} g`. So the discrepancy
  `e_b⁻¹ ∘ e_{b'}` between the two local isomorphisms is the automorphism of `G` given by
  the point `x` of `Gad` through `c`.
- `IsRelativeBorelSubgroup i` (Conrad Definition 5.2.10): `i` is a relative parabolic
  subgroup whose residue fibres are Borel subgroups that stay Borel over an algebraic
  closure of the residue field.
- `IsRelativeQuasiSplit G'` (Conrad Definition 5.2.10): `G'` is reductive and has a Borel
  subgroup over the base.
- `RelativeTorus.IsTorus T'.toGrp`: there is an étale cover of `S` over each member of
  which `T'` becomes a split torus.
- `IsClosedSubgroup t`: the underlying morphism of schemes `T' ⟶ G'` is a closed immersion.
- `IsFibrewiseMaximalTorus t`: for every point `s` of `S`, the residue fibre of `t` over
  `κ(s)` satisfies the field predicate `IsMaximalTorus` in `G'_s`
  ([`Torus.Maximal`](../Torus/Maximal.md)).
- `SubgroupFunctor.range f`: the image of `f` as a subgroup functor of its target; `≤` is
  inclusion of subgroup functors.

## Statement and quantifiers

The proposition quantifies over every scheme `S : Scheme.{u}`, every `G : GroupScheme S`
with `IsReductive G`, every `Gad : GroupScheme S` and `p : G ⟶ Gad` with
`RelativeRoot.IsFppfQuotient (center G) p`, and every `c : AutomorphicAction Gad G` with
`c.restrict p = AutomorphicAction.conjugation (𝟙 G)`.

It asserts that there is `G' : GroupScheme S` such that:

1. (inner form) there are `U : Over S` with `Etale U.hom` and `Surjective U.hom`, and
   `e : LocalGroupIso G G' U` with `e.HasInnerDiscrepancy c`;
2. (quasi-split) `IsRelativeQuasiSplit G'`;
3. (Borel subgroup through a maximal torus) there are `B' : GroupScheme S`,
   `i : B' ⟶ G'`, `T' : CommGroupScheme S` and `t : T'.toGrp ⟶ G'` with
   `IsRelativeBorelSubgroup i`, `RelativeTorus.IsTorus T'.toGrp`, `IsClosedSubgroup t`,
   `IsFibrewiseMaximalTorus t` and `SubgroupFunctor.range t ≤ SubgroupFunctor.range i`.

Item 2 follows from item 3 and the reductivity of `G'`; it is stated separately to name the
conclusion of the source.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the one-based PDF pages, which agree with the printed page numbers.

- p.258, before Proposition 7.2.11: "It is a very useful fact (for the classification of
  forms and other purposes) that over any non-empty scheme S every reductive S-group G has
  an inner form that is quasi-split (see Definition 5.2.10)."
- Proposition 7.2.11, p.258: "Let S be a non-empty scheme, (G0, T0, M) a split reductive
  S-group with root datum R, and G a reductive S-group whose geometric fibers have root
  datum R. There exists a quasi-split inner form G′ of G such that Aut_{G′/S} → Out_{G′/S}
  has an S-group section, some Borel subgroup B′ ⊂ G′ contains a maximal torus T′ of G′,
  and T′/Z_{G′} ≃ R_{S′/S}(G_m) for a finite étale cover S′ → S."
- Proof of Proposition 7.2.11, p.258. It twists the split form `G0` by the image of the
  class of `G` under the section `Θ → Aut(G0)` defined by a pinning, where `Θ = Aut(R, ∆)`.
  The twisting cocycle preserves `T0` and the Borel subgroup `B0 ⊇ T0`, so `G′` has a
  maximal torus `T′` and a Borel subgroup `B′ ⊇ T′`; by Exercise 7.3.8, `G′` is an inner
  form of `G`.
- Inner forms, p.253: "Consider a reductive group G over a non-empty scheme S. The inner
  forms of G are the forms of G that correspond to the image of H¹(S_ét, G/Z_G) in
  H¹(S_ét, Aut_{G/S})."
- Definition 5.2.10, p.157: "A Borel subgroup of a reductive group scheme G → S is a
  parabolic subgroup P ⊂ G such that P_s is a Borel subgroup of G_s for all s ∈ S. A
  reductive group G → S is quasi-split over S if it admits a Borel subgroup scheme over S."

## Derivation from the source

- **Base and root datum.** The statement takes any scheme `S` and any reductive `G`, as in
  the sentence on p.258 that precedes Proposition 7.2.11. The proposition itself assumes
  that the geometric fibres of `G` all have one root datum `R`. Over a general `S` the
  root datum of the geometric fibres is locally constant (reductive groups are split
  étale-locally, and étale maps are open), so `S` is the disjoint union of open and
  closed subschemes `S_R` on which it is constant. Proposition 7.2.11 applies to each
  non-empty `G_{S_R}` (a split `S_R`-group with root datum `R` exists by the existence
  theorem), and the resulting inner forms, Borel subgroups and maximal tori over the
  `S_R` glue to ones over `S`. Over the empty scheme the statement holds trivially. So the
  Lean statement is the sentence on p.258 with the Borel and torus clause of
  Proposition 7.2.11.
- **`G/Z_G` and its action.** As in `ReductiveConnectedActionInnerStatement`
  (Proposition 7.2.6) and `ReductiveSemilocalQuasiSplitInnerFormStatement`
  (Proposition 7.2.12), `G/Z_G` is a group scheme `Gad` with an fppf quotient map
  `p : G ⟶ Gad` whose kernel has range `center G`, and its natural action on `G` is the
  action `c` whose restriction along `p` is conjugation. Since `p × 𝟙 : G × G → Gad × G` is
  an fppf epimorphism, at most one such `c` exists.
- **Inner forms.** A form `G′` of `G` is given by an étale cover of `S` and isomorphisms
  `G_U ≅ G′_U` on it. Its class in `H¹(S_ét, Aut_{G/S})` is the cocycle of discrepancies of
  these isomorphisms on the overlaps. The class lies in the image of `H¹(S_ét, G/Z_G)`
  exactly when, for some such cover and isomorphisms, every discrepancy is the action of a
  point of `G/Z_G`. In the encoding the cover is one étale surjective morphism `U ⟶ S` (a
  disjoint union of the members of a cover), the isomorphisms are
  `e : LocalGroupIso G G' U`, and the condition on the discrepancies is
  `e.HasInnerDiscrepancy c`. Every pair of points `b b' : T ⟶ U` factors through the
  overlap `U ×_S U`, so this is the condition on overlaps. This is the same encoding as in
  `ReductiveSemilocalQuasiSplitInnerFormStatement`.
- **Quasi-split.** `IsRelativeQuasiSplit` is the Library transcription of Definition 5.2.10.
  Conrad notes there that SGA3's relative notion has additional requirements, and that
  Definition 5.2.10 is the one used in his notes.
- **"Some Borel subgroup B′ ⊂ G′ contains a maximal torus T′ of G′".** `T′` is given
  abstractly with `t : T′ ⟶ G′`. The conditions `RelativeTorus.IsTorus`,
  `IsClosedSubgroup` and `IsFibrewiseMaximalTorus` say that `t` is a maximal torus of `G′`,
  with the encoding of the published `RelativeOppositeBorelStatement` and
  `TorusLeviStatement`: `RelativeTorus.IsTorus` is étale-local splitting, which by
  Proposition B.3.4 is equivalent to being an `S`-torus; closedness adds nothing by
  Lemma B.1.3; and maximality on residue fibres agrees with maximality on geometric fibres
  by Remark A.1.2. Containment in `B′` is inclusion of images as subgroup functors of `G′`.

## Scope

All objects are in universe `u`. `S` is any scheme; it may be empty, non-Noetherian or
disconnected. No splitting of `G`, maximal torus, Borel subgroup or constancy of the root
datum of `G` is assumed.

## Not stated

The statement does not assert that the quotient `G/Z_G` or the action `c` exist (Conrad
§3.3 and Theorem 7.1.9); without such `Gad`, `p` and `c` it holds vacuously. It omits two
conclusions of Proposition 7.2.11: that `Aut_{G′/S} → Out_{G′/S}` has an `S`-group section
(the automorphism scheme is not available over a general base), and that
`T′/Z_{G′} ≃ R_{S′/S}(G_m)` for a finite étale cover `S′ → S`. It does not state the
uniqueness of the quasi-split inner form over a semi-local base (Proposition 7.2.12, stated
separately as `ReductiveSemilocalQuasiSplitInnerFormStatement`), and it does not state that
being an inner form is an equivalence relation.
