# Statement: maximal tori and parabolic subgroups of a reductive group and its derived group

Worker 75.

`Langlands.GroupScheme.ReductiveDerivedTorusParabolicCorrespondenceStatement.{u} : Prop`
is a statement-only, `Prop`-valued definition. This module does not prove it, and it adds
no other definitions, theorems or axioms. It imports:

- [`Reductive.Semisimple`](Semisimple.md), for the field predicate `IsSemisimple`;
  `IsReductive`, `geometricFiber` and `IsClosedSubgroup` come transitively from
  [`Reductive.Basic`](Basic.md);
- [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md),
  for `RelativeRoot.IsFppfQuotient`;
- [`Rational.SplitTorusFactorization`](../Rational/SplitTorusFactorization.md), for the
  product homomorphism `prodHom` and `IsCentral.commute_values`;
- [`Torus.FieldPointMaximality`](../Torus/FieldPointMaximality.md), for
  `IsFibrewiseMaximalTorus`;
- [`Torus.Relative`](../Torus/Relative.md), for `RelativeTorus.IsTorus`;
- [`CentralIsogeny.Basic`](../CentralIsogeny/Basic.md), for `IsCentralIsogeny`, and
  transitively [`AbelianScheme.Isogeny`](../../AbelianScheme/Isogeny.md), for
  `IsIsogeny`;
- [`SubgroupIntersection`](../SubgroupIntersection.md), for `subgroupIntersection`,
  `subgroupIntersectionFst` and `subgroupIntersectionHom`;
- [`RelativeLevi.Basic`](../RelativeLevi/Basic.md), for `IsRelativeParabolicSubgroup`.

`IsCentral` comes from [`Rational.Characters`](../Rational/Characters.md).
`SubgroupFunctor.range` and `SubgroupFunctor.IsNormal` come from
[`SubgroupFunctor`](../SubgroupFunctor.md). In the cartesian monoidal category
`GroupScheme S` (`Grp (Over S)`), the tensor product `⊗` is the product of group schemes;
the module opens `CategoryTheory.MonoidalCategory` for this notation.

## Predicates and constructions used

- `IsClosedSubgroup i`: the underlying morphism of schemes of `i` is a closed immersion.
- `IsCentral i`: for every `T : Over S` and every `T`-point `x` of the source, the point
  `x ≫ i` lies in the centre of the target, that is, every restriction of it commutes
  with every point of the target over the same test scheme.
- `RelativeTorus.IsTorus T`: `T` becomes a finite split torus on some étale cover of `S`.
- `IsFibrewiseMaximalTorus t`: for every point `s` of `S`, the residue fibre of `t` over
  `κ(s)` satisfies the field predicate `IsMaximalTorus`
  ([`Torus.Maximal`](../Torus/Maximal.md)).
- `RelativeRoot.IsFppfQuotient N q`: the underlying morphism of `q` is flat, surjective
  and locally of finite presentation, and the range of the scheme kernel of `q` is `N`.
- `IsIsogeny f`: the underlying morphism of schemes of `f` is finite, flat and
  surjective.
- `IsCentralIsogeny f`: `IsIsogeny f`, the underlying morphism of `f` is locally of
  finite presentation, and the inclusion of the scheme kernel of `f` into the source is
  central.
- `IsRelativeParabolicSubgroup i` (Conrad Definition 5.2.1): the source of `i` is smooth
  and affine over `S`, `i` is a monomorphism of schemes, and every residue fibre of `i`
  is a parabolic subgroup.
- `subgroupIntersection j j'` is the fibre product of `j : P ⟶ G` and `j' : P' ⟶ G`
  over `G`, the intersection of the two subgroups. `subgroupIntersectionFst j j'` is its
  projection to `P`, and `subgroupIntersectionHom j j'` is that projection followed by
  `j`. Its points on a test scheme are pairs of points of `P` and `P'` with the same
  image in `G`.
- `prodHom a b h : A ⊗ B ⟶ G` is the homomorphism `(x, y) ↦ a(x) * b(y)` on points. The
  argument `h` is the proof that the values of `a` and `b` commute; here it is always
  `hz.commute_values _` for `hz : IsCentral z`.

## The local predicates

After the binders `S` and `G`, the statement introduces two local `let`s.

- `IsMaximalCentralTorus z`, for `Z : GroupScheme S` and `z : Z ⟶ G`, is the conjunction
  of `IsClosedSubgroup z`, `IsCentral z`, `RelativeTorus.IsTorus Z`, and: for every
  `Z' : GroupScheme S` and `z' : Z' ⟶ G` with `IsClosedSubgroup z'`, `IsCentral z'` and
  `RelativeTorus.IsTorus Z'`, `SubgroupFunctor.range z' ≤ SubgroupFunctor.range z`. It
  is the same predicate as in `ReductiveDerivedCentralIsogenyStatement`
  (Corollary 5.3.3).
- `IsMaxTorus t`, for `H : GroupScheme S`, `T : CommGroupScheme S` and
  `t : T.toGrp ⟶ H`, is the conjunction of `RelativeTorus.IsTorus T.toGrp`,
  `IsClosedSubgroup t` and `IsFibrewiseMaximalTorus t`: `t` is a maximal torus of `H`.
  It is used both for `H = G` and for `H = D`.

## Statement and quantifiers

The proposition quantifies over every scheme `S : Scheme.{u}` and every group scheme
`G : GroupScheme S` with `IsReductive G`; then over every `D : GroupScheme S` and
`d : D ⟶ G` with

- `IsClosedSubgroup d`,
- `(SubgroupFunctor.range d).IsNormal`,
- `IsReductive D` and `IsSemisimple (geometricFiber D s)` for every point `s : S`,
- the existence of `Q : GroupScheme S` and `q : G ⟶ Q` with `RelativeTorus.IsTorus Q`
  and `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q`;

and over every `Z : GroupScheme S`, `z : Z ⟶ G` and `hz : IsCentral z` with
`IsMaximalCentralTorus z`. It asserts the conjunction of six items.

Maximal tori:

1. For every `T : CommGroupScheme S` and `t : T.toGrp ⟶ G` with `IsMaxTorus t`:
   - there are `T' : CommGroupScheme S` and `t' : T'.toGrp ⟶ D` with `IsMaxTorus t'`
     and `SubgroupFunctor.range t' =
     SubgroupFunctor.range (subgroupIntersectionFst d t)`; and
   - there is `e : Z ⊗ subgroupIntersection d t ⟶ T.toGrp` with `IsIsogeny e` and
     `e ≫ t = prodHom z (subgroupIntersectionHom d t) (hz.commute_values _)`.
2. For every `T' : CommGroupScheme S` and `t' : T'.toGrp ⟶ D` with `IsMaxTorus t'`,
   there are `T : CommGroupScheme S`, `t : T.toGrp ⟶ G` and
   `e : Z ⊗ T'.toGrp ⟶ T.toGrp` with `IsMaxTorus t`, `IsIsogeny e`,
   `e ≫ t = prodHom z (t' ≫ d) (hz.commute_values _)` and
   `SubgroupFunctor.range (subgroupIntersectionFst d t) = SubgroupFunctor.range t'`.
3. For all `T₁ T₂ : CommGroupScheme S`, `t₁ : T₁.toGrp ⟶ G` and `t₂ : T₂.toGrp ⟶ G`
   with `IsMaxTorus t₁` and `IsMaxTorus t₂`, if
   `SubgroupFunctor.range (subgroupIntersectionFst d t₁) =
   SubgroupFunctor.range (subgroupIntersectionFst d t₂)` then
   `SubgroupFunctor.range t₁ = SubgroupFunctor.range t₂`.

Parabolic subgroups:

4. For every `P : GroupScheme S` and `i : P ⟶ G` with `IsRelativeParabolicSubgroup i`:
   `IsRelativeParabolicSubgroup (subgroupIntersectionFst d i)`, and there is
   `e : Z ⊗ subgroupIntersection d i ⟶ P` with `IsCentralIsogeny e` and
   `e ≫ i = prodHom z (subgroupIntersectionHom d i) (hz.commute_values _)`.
5. For every `P' : GroupScheme S` and `i' : P' ⟶ D` with
   `IsRelativeParabolicSubgroup i'`, there are `P : GroupScheme S`, `i : P ⟶ G` and
   `e : Z ⊗ P' ⟶ P` with `IsRelativeParabolicSubgroup i`, `IsCentralIsogeny e`,
   `e ≫ i = prodHom z (i' ≫ d) (hz.commute_values _)` and
   `SubgroupFunctor.range (subgroupIntersectionFst d i) = SubgroupFunctor.range i'`.
6. For all `P₁ P₂ : GroupScheme S`, `i₁ : P₁ ⟶ G` and `i₂ : P₂ ⟶ G` with
   `IsRelativeParabolicSubgroup i₁` and `IsRelativeParabolicSubgroup i₂`, if
   `SubgroupFunctor.range (subgroupIntersectionFst d i₁) =
   SubgroupFunctor.range (subgroupIntersectionFst d i₂)` then
   `SubgroupFunctor.range i₁ = SubgroupFunctor.range i₂`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the one-based PDF pages, which agree with the printed page numbers.

- Proposition 5.3.4, p.164: "Let G → S be a reductive group scheme, and Z the maximal
  torus of Z_G. The map T ↦ T ∩ D(G) is a bijective correspondence between the set of
  maximal tori in G and the set of maximal tori in D(G). Conversely, if T′ is a maximal
  torus of D(G) then T′ × Z → G is an isogeny onto a maximal torus T of G, and this
  reverses the bijective correspondence. The same holds for parabolic subgroups, with
  the analogous procedures using intersection and product against Z."
- Proof of Proposition 5.3.4, pp.164–165. For tori: `T ∩ D(G)` is a torus (by
  Example 2.2.6, since `T` normalizes `D(G)`), the classical theory makes it a maximal
  torus of `D(G)`, and "if we define T′ := T ∩ D(G) then the multiplication map
  Z × T′ → T between tori is an isogeny"; conversely, for a maximal torus `T′` of
  `D(G)`, "T′ × Z → G is an isogeny onto a maximal torus of G", checked on geometric
  fibres via `Z_G(T′)`. For parabolics: `Z_G ⊂ P` for every parabolic `P`, so "the
  isogeny Z × D(G) → G implies that P is uniquely determined by P′ = P ∩ D(G)"; `P′` is
  parabolic in `D(G)`; "The multiplication map m : Z × P′ → P is an isogeny on fibers,
  so m is a quasi-finite flat surjection, and ker m is visibly central. But ker m is
  closed in the S-finite kernel of Z × D(G) → G, so it is S-finite and hence m is a
  central isogeny"; and every parabolic `Q` of `D(G)` is `P ∩ D(G)` for a parabolic `P`
  of `G`, by étale localization and Proposition 5.2.3.
- Theorem 5.3.1, p.160: `D(G)` is the unique semisimple closed normal `S`-subgroup of
  `G` such that `G/D(G)` is a torus.
- Corollary 5.3.3, p.164: `Z × D(G) → G` is a central isogeny.
- Definition 3.3.9, p.103: "A homomorphism f : G′ → G between smooth S-affine S-groups
  is an isogeny if it is a finite flat surjection, and is a central isogeny if also
  ker f is central in G′."
- Definition 3.1.1, p.81: an `S`-torus is an `S`-group of multiplicative type with smooth
  connected fibres; a semisimple `S`-group is a reductive `S`-group whose geometric fibres
  are semisimple.
- Definition 3.2.1, p.91: "A maximal torus in a smooth S-affine group scheme G → S is a
  torus T ⊂ G such that for each geometric point s̄ of S the fiber T_s̄ is not contained
  in any strictly larger torus in G_s̄."
- Remark A.1.2, p.267: over a field `k`, maximality of a `k`-torus in the geometric
  sense of Definition 3.2.1 is the same as maximality among `k`-tori.
- Proposition B.3.4, pp.290–291: a group of multiplicative type is diagonalizable
  étale-locally on `S`.
- Definition 5.2.1, p.151: parabolic subgroups over a base.

## Derivation from the source

- **`D(G)`.** As in `ReductiveDerivedCentralIsogenyStatement`, the derived group is
  encoded by its defining properties from Theorem 5.3.1: a closed subgroup `d` with
  normal range, `D` semisimple, and some represented fppf quotient of `G` by the range of
  `d` that is an `S`-torus. By the uniqueness in Theorem 5.3.1 these single out `D(G)`
  up to the choice of closed embedding with that range. The quotient enters only as a
  hypothesis, so it is quantified existentially.
- **`Z`.** "The maximal torus of Z_G" is `IsMaximalCentralTorus z`, the predicate of the
  Corollary 5.3.3 statement. The separate binder `hz : IsCentral z` repeats one conjunct
  of that predicate. It is needed to form `prodHom`, whose third argument is a proof
  that the values of `z` commute with those of the other factor.
- **Maximal tori.** `IsMaxTorus` is the encoding of a maximal torus used by the published
  `TorusLeviStatement`: `RelativeTorus.IsTorus` is étale-local splitting, equivalent to
  being an `S`-torus by Proposition B.3.4; the closed-subgroup condition is the inclusion
  `T ⊂ G`; and maximality on residue fibres agrees with maximality on geometric fibres by
  Remark A.1.2.
- **`T ∩ D(G)` and `P ∩ D(G)`.** The intersection is `subgroupIntersection d t`, viewed as
  a subgroup of `D` through `subgroupIntersectionFst d t`. Because `d` and `t` are
  monomorphisms, its range in `D` is the subfunctor of points of `D` whose image in `G`
  lies in `T`. "T ∩ D(G) is a maximal torus of D(G)" is stated as equality of this range
  with the range of some maximal torus `t'` of `D`, since the fibre product is a
  `GroupScheme` rather than a `CommGroupScheme`.
- **The bijection.** The map `T ↦ T ∩ D(G)` of the source is stated through its
  properties: it is well defined (items 1 and 4, first parts), surjective with the
  inverse given by product with `Z` (items 2 and 5), and injective (items 3 and 6).
  Subgroups are compared by their ranges as subgroup functors, so two embeddings with
  the same image count as the same subgroup.
- **"T′ × Z → G is an isogeny onto T".** Multiplication is
  `prodHom z (t' ≫ d) (hz.commute_values _)`, written with the factors in the order
  `Z ⊗ T′`. "An isogeny onto T" is a factorization `e ≫ t` of the multiplication through
  the maximal torus `t` with `e` an isogeny. Since `t` is a monomorphism, `e` is
  determined by the multiplication. The statement does not say that the image of the
  multiplication, as a pointwise image of subgroup functors, equals the range of `t`.
  The pointwise image of a finite flat surjection need not contain every point of the
  target, so that equality would be false in general.
- **The reverse direction for tori and for parabolics.** Items 1 and 4 also state that
  multiplication `Z × (T ∩ D(G)) → T` is an isogeny, and `Z × (P ∩ D(G)) → P` a central
  isogeny. The proof states both. For tori this is the source's reverse map applied to
  `T′ = T ∩ D(G)`.
- **"Isogeny" and "central isogeny".** "Isogeny" is `IsIsogeny`, the finite flat
  surjection of Definition 3.3.9, as in the source's wording for tori. For parabolics the
  proof concludes that `m : Z × P′ → P` "is a central isogeny", stated with
  `IsCentralIsogeny`. That predicate adds local finite presentation to Definition 3.3.9.
  The groups involved are of finite presentation over `S`, and a morphism between
  `S`-schemes locally of finite presentation is locally of finite presentation, so the
  source's maps satisfy the extra condition.
- **Parabolic subgroups.** `IsRelativeParabolicSubgroup` is the Library's transcription
  of Definition 5.2.1, applied to `i : P ⟶ G` and to `subgroupIntersectionFst d i` and
  `i' : P' ⟶ D` inside `D`.

## Scope

All objects are in universe `u`. The base `S` is an arbitrary scheme: it need not be
affine, Noetherian, reduced or connected, and the empty scheme is allowed. No splitting of
`G` and no global maximal torus of `G` is assumed.

## Not stated

The statement does not assert that `D(G)`, its torus quotient, or the maximal central
torus `Z` exist. These are Theorem 5.3.1 (`RelativeDerivedGroupStatement`) and
Corollary 5.3.3 (`ReductiveDerivedCentralIsogenyStatement`), separate statement candidates
that this module does not import. Without such `d`, `Q` and `z` the statement holds
vacuously. The facts used in the proof but not part of the proposition are not stated:
that `T ∩ D(G)` is smooth with connected fibres, that `Z_G ⊂ P` for every parabolic `P`,
and that `Z_G(T′)` is a torus.
