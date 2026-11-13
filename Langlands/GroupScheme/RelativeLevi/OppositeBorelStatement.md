# Statement: the unique Borel subgroup opposite to a Borel subgroup through a maximal torus

Worker 75.

`Langlands.GroupScheme.RelativeOppositeBorelStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other
definitions, theorems or axioms. It imports [`RelativeLevi.Borel`](Borel.md), for
`IsRelativeBorelSubgroup`, [`Torus.FieldPointMaximality`](../Torus/FieldPointMaximality.md),
for `IsFibrewiseMaximalTorus`, and [`Torus.Relative`](../Torus/Relative.md), for
`RelativeTorus.IsTorus`.

## Statement and quantifiers

The proposition quantifies over:

- every scheme `S : Scheme.{u}`;
- group schemes `G B : GroupScheme S` and a homomorphism `i : B ⟶ G`;
- a commutative group scheme `T : CommGroupScheme S` and a homomorphism
  `t : T.toGrp ⟶ G`.

It has six hypotheses:

1. `IsReductive G` ([`Reductive.Basic`](../Reductive/Basic.md)): `G` is smooth and
   affine over `S`, and its geometric fibres are connected reductive groups.
2. `RelativeTorus.IsTorus T.toGrp`: there is an étale cover of `S` over each member of
   which `T` becomes a split torus.
3. `IsClosedSubgroup t`: the underlying morphism of schemes `T ⟶ G` is a closed
   immersion.
4. `IsFibrewiseMaximalTorus t`: for every point `s` of `S`, the residue fibre of `t` over
   `κ(s)` satisfies the field predicate `IsMaximalTorus` in `G_s`
   ([`Torus.Maximal`](../Torus/Maximal.md)).
5. `IsRelativeBorelSubgroup i` ([`RelativeLevi.Borel`](Borel.md)): `i` is a parabolic
   subgroup in the sense of `IsRelativeParabolicSubgroup`, and every residue fibre of `i`
   satisfies `IsGeometricBorelSubgroup`.
6. `SubgroupFunctor.range t ≤ SubgroupFunctor.range i`: on every test scheme, every
   point of `G` that factors through `t` factors through `i`, so `T ⊆ B`.

The conclusion is: there are `B' : GroupScheme S` and `i' : B' ⟶ G` such that

- `IsRelativeBorelSubgroup i'`;
- `SubgroupFunctor.range i' ⊓ SubgroupFunctor.range i = SubgroupFunctor.range t`: on
  every test scheme `T₀` over `S`, a point of `G(T₀)` lies in both `B'(T₀)` and `B(T₀)`
  exactly when it lies in `T(T₀)`. The infimum `⊓` of subgroup functors is the pointwise
  intersection ([`SubgroupFunctor`](../SubgroupFunctor.md));
- for every `B'' : GroupScheme S` and `i'' : B'' ⟶ G` with `IsRelativeBorelSubgroup i''`
  and `SubgroupFunctor.range i'' ⊓ SubgroupFunctor.range i = SubgroupFunctor.range t`,
  the images agree: `SubgroupFunctor.range i'' = SubgroupFunctor.range i'`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the one-based PDF pages, which agree with the printed page numbers.

- Proposition 5.2.12, p.158: "Let G → S be a reductive group scheme, and T ⊂ G a
  maximal torus. If B ⊂ G is a Borel subgroup containing T then there exists a unique
  Borel subgroup B′ ⊂ G satisfying B′ ∩ B = T."
- Proof of Proposition 5.2.12, p.158. Étale-locally `B = P_G(λ)` for a cocharacter `λ`
  of a split `T`, `T = Z_G(λ)`, and `B′ := P_G(−λ)` satisfies `B′ ∩ B = Z_G(λ) = T` by
  Theorem 4.1.7(4). Uniqueness is reduced by Corollary 5.2.7(2) to geometric fibres,
  which is Proposition 1.4.4.
- Definition 5.2.10, p.157 (Borel subgroups over a base).
- Definition 3.1.1, p.81: "An S-torus is an S-group T → S of multiplicative type with
  smooth connected fibers."
- Definition 3.2.1, p.91: "A maximal torus in a smooth S-affine group scheme G → S is a
  torus T ⊂ G such that for each geometric point s̄ of S the fiber T_s̄ is not contained
  in any strictly larger torus in G_s̄."
- Remark A.1.2, p.267: over a field `k`, maximality of a `k`-torus in the geometric
  sense of Definition 3.2.1 is the same as maximality among `k`-tori.
- Proposition B.3.4, pp.290–291: a group of multiplicative type is diagonalizable
  étale-locally on `S`.
- Lemma B.1.3, p.281: a monic homomorphism from a group of multiplicative type to an
  `S`-affine `S`-group of finite presentation is a closed immersion.

## Derivation from the source

The proposition is Proposition 5.2.12, with its terms translated as follows.

- **"T ⊂ G a maximal torus".** `T` is given abstractly with `t : T ⟶ G`. Hypotheses
  2–4 say that `t` is a maximal torus of `G`, with the encoding of the published
  [`TorusLeviStatement`](TorusLeviStatement.md): `RelativeTorus.IsTorus` is étale-local
  splitting, which by Proposition B.3.4 is equivalent to being an `S`-torus;
  closedness adds nothing by Lemma B.1.3; and maximality on residue fibres agrees with
  maximality on geometric fibres by Remark A.1.2.
- **"B ⊂ G a Borel subgroup containing T".** Hypothesis 5 uses the published predicate
  `IsRelativeBorelSubgroup`, the Library's transcription of Definition 5.2.10, and
  hypothesis 6 is inclusion of images as subgroup functors of `G`.
- **"B′ ∩ B = T".** The intersection of two subgroups of `G` is their fibre product
  over `G`. Its points on a test scheme are the points of `G` lying in both subgroups,
  so its functor of points is the pointwise intersection of the two image functors.
  Because `i`, `i'` and `t` are monomorphisms, equality with `T` is the equality of
  subgroup functors in the conclusion.
- **"Unique".** Two Borel subgroups are given as abstract group schemes with
  monomorphisms into `G`. They are the same subgroup of `G` exactly when their images
  agree as subgroup functors, as in the other uniqueness statements of this directory.
  The third clause of the conclusion states that every Borel subgroup `B''` with
  `B'' ∩ B = T` has the same image as `B'`.

## Scope

All objects are in universe `u`. The base `S` is an arbitrary scheme: it need not be
affine, Noetherian, reduced or connected, and the empty scheme is allowed. `T` need not
be split over `S`, and no cocharacter or splitting is given.

## Relation to the Library

- [`TorusLeviStatement`](TorusLeviStatement.md) states Proposition 5.4.5 (the unique
  Levi subgroup of a parabolic subgroup containing a given maximal torus) with the same
  encoding of maximal tori and of uniqueness.

This module proves no relation to other statements.
