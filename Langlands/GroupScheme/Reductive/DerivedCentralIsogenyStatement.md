# Statement: central isogenies from the derived group and the maximal central torus

Worker 75.

`Langlands.GroupScheme.ReductiveDerivedCentralIsogenyStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Reductive.Semisimple`](Semisimple.md), for the field predicate `IsSemisimple`;
  `IsReductive`, `geometricFiber` and `IsClosedSubgroup` come transitively from
  [`Reductive.Basic`](Basic.md);
- [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md),
  for `RelativeRoot.IsFppfQuotient`;
- [`Rational.SplitTorusFactorization`](../Rational/SplitTorusFactorization.md), for the
  product homomorphism `prodHom` and `IsCentral.commute_values`;
- [`Torus.Relative`](../Torus/Relative.md), for `RelativeTorus.IsTorus`;
- [`CentralIsogeny.Basic`](../CentralIsogeny/Basic.md), for `IsCentralIsogeny`.

`IsCentral` and `center` come from [`Rational.Characters`](../Rational/Characters.md).
`SubgroupFunctor.range` and `SubgroupFunctor.IsNormal` come from
[`SubgroupFunctor`](../SubgroupFunctor.md). `CartesianMonoidalCategory.lift` is
Mathlib's pairing morphism in the cartesian monoidal category `GroupScheme S`
(`Grp (Over S)`), whose tensor product `⊗` is the product of group schemes.

## Predicates used

- `IsClosedSubgroup i`: the underlying morphism of schemes of `i` is a closed immersion.
- `IsCentral i`: for every `T : Over S` and every `T`-point `x` of the source, the point
  `x ≫ i` lies in the centre `center G`, that is, every restriction of it commutes with
  every point of `G` over the same test scheme.
- `RelativeTorus.IsTorus Z`: `Z` becomes a finite split torus on some étale cover of `S`.
- `RelativeRoot.IsFppfQuotient N q`: the underlying morphism of `q` is flat, surjective
  and locally of finite presentation, and the range of the scheme kernel of `q` is `N`.
- `IsCentralIsogeny f`: the underlying morphism of `f` is finite, flat, surjective and
  locally of finite presentation, and the inclusion of the scheme kernel of `f` into the
  source is central.
- `prodHom z d h : Z ⊗ D ⟶ G` is the homomorphism `(x, y) ↦ z(x) * d(y)` on points. The
  argument `h` is the proof that the values of `z` and `d` commute, here
  `hz.commute_values d` for `hz : IsCentral z`.
- `CartesianMonoidalCategory.lift q p : G ⟶ Q ⊗ P` is the homomorphism with components
  `q` and `p`.

## The local predicate `IsMaximalCentralTorus`

After the binders `S` and `G`, the statement introduces a local `let`. For
`Z : GroupScheme S` and `z : Z ⟶ G`, `IsMaximalCentralTorus z` is the conjunction of
`IsClosedSubgroup z`, `IsCentral z`, `RelativeTorus.IsTorus Z`, and: for every
`Z' : GroupScheme S` and `z' : Z' ⟶ G` with `IsClosedSubgroup z'`, `IsCentral z'` and
`RelativeTorus.IsTorus Z'`,
`SubgroupFunctor.range z' ≤ SubgroupFunctor.range z`.

## Statement and quantifiers

The proposition quantifies over every scheme `S : Scheme.{u}` and every group scheme
`G : GroupScheme S` with `IsReductive G`, and asserts the conjunction of:

1. **Existence of the maximal central torus.** There are `Z : GroupScheme S` and
   `z : Z ⟶ G` with `IsMaximalCentralTorus z`.
2. **Central isogenies.** For every `D : GroupScheme S` and `d : D ⟶ G` with
   `IsClosedSubgroup d`, normal range, `IsReductive D` and
   `IsSemisimple (geometricFiber D s)` for every point `s : S`; for every
   `Q : GroupScheme S` and `q : G ⟶ Q` with `RelativeTorus.IsTorus Q` and
   `RelativeRoot.IsFppfQuotient (range d) q`; and for every `Z : GroupScheme S`,
   `z : Z ⟶ G` and `hz : IsCentral z` with `IsMaximalCentralTorus z`:
   1. `IsCentralIsogeny (prodHom z d (hz.commute_values d))`;
   2. for every `P : GroupScheme S` and `p : G ⟶ P` with
      `RelativeRoot.IsFppfQuotient (range z) p`,
      `IsCentralIsogeny (CartesianMonoidalCategory.lift q p)`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the one-based PDF pages, which agree with the printed page numbers.

- Corollary 5.3.3, p.164: "Let G → S be a reductive group scheme, D(G) its derived
  group. Let Z ⊂ Z_G be the maximal central torus of G, and T′ = G/D(G) the maximal
  torus quotient. The natural S-homomorphisms f : Z × D(G) → G and
  h : G → T′ × (G/Z) are central isogenies."
- Proof of Corollary 5.3.3, p.164: the classical theory shows that `f_s` and `h_s` are
  central isogenies for every `s`, and Proposition 3.3.10 concludes. "See Remark B.1.2
  for the existence and compatibility with base change of a subtorus containing all
  others in any multiplicative type group, thereby providing Z inside Z_G compatibly
  with any base change."
- Theorem 5.3.1, p.160: `D(G)` is the unique semisimple closed normal `S`-subgroup of
  `G` such that `G/D(G)` is a torus.
- Definition 3.3.9, p.103: "A homomorphism f : G′ → G between smooth S-affine S-groups
  is an isogeny if it is a finite flat surjection, and is a central isogeny if also
  ker f is central in G′."
- Definition 3.1.1, p.81: a semisimple `S`-group is a reductive `S`-group whose
  geometric fibres are semisimple.
- Theorem 3.3.4, p.98: the scheme-theoretic centre `Z_G` of a reductive group is the
  reductive centre, in particular a central subgroup of multiplicative type.

## Derivation from the source

- "D(G) its derived group" and "T′ = G/D(G) the maximal torus quotient" are encoded by
  the hypotheses on `d` and `q`. They are the defining properties of `D(G)` in
  Theorem 5.3.1 (semisimple, closed, normal, with torus quotient), the same conditions
  as the local predicate `Admissible` of `RelativeDerivedGroupStatement` (module
  `Langlands.GroupScheme.Reductive.RelativeDerivedGroupStatement`, a separate statement
  candidate that this module does not import). By the
  uniqueness in Theorem 5.3.1 they single out `D(G)` up to the choice of closed
  embedding with that range. The statement quantifies over every such `d` and every
  represented fppf quotient `q` by its range with torus target.
- "Z ⊂ Z_G the maximal central torus" is `IsMaximalCentralTorus z`. By Theorem 3.3.4,
  subtori of `Z_G` are the closed central subgroups of `G` that are `S`-tori, and the
  maximal central torus is the one containing all others. Item 1 asserts that it
  exists, as the proof of Corollary 5.3.3 notes via Remark B.1.2.
- "The natural S-homomorphism f : Z × D(G) → G" is multiplication,
  `prodHom z d (hz.commute_values d)`. It is a homomorphism because `Z` is central.
- "h : G → T′ × (G/Z)" is `CartesianMonoidalCategory.lift q p`, where `p` is a
  represented fppf quotient of `G` by the range of `z`.
- "Central isogeny" is `IsCentralIsogeny`, which is Definition 3.3.9 together with the
  condition that the morphism is locally of finite presentation. In the source, the
  groups `Z × D(G)`, `G` and `T′ × (G/Z)` are of finite presentation over `S` (the
  quotient by a central multiplicative type subgroup is "represented by an S-affine
  S-scheme of finite presentation", p.98), and a morphism between `S`-schemes locally of
  finite presentation is locally of finite presentation. So the corollary's maps satisfy
  the extra condition.
- An `S`-torus is taken in the étale-local sense `RelativeTorus.IsTorus`, which is
  equivalent to Definition 3.1.1 by Proposition B.3.4 of the source.

## Scope

All objects are in universe `u`. The base `S` is an arbitrary scheme: it need not be
affine, Noetherian, reduced or connected, and the empty scheme is allowed. No maximal
torus or splitting of `G` is assumed.

## Not stated

The statement does not assert that a represented fppf quotient `G/Z` exists. The source
takes `G/Z` from the theory of quotients by central subgroups of multiplicative type
(Lemma 3.3.1(2), citing SGA3 VIII 5.1 and IX 2.3), not from the proof of
Corollary 5.3.3. Item 2.2 is a claim about every such quotient. The existence of `D(G)`
and of `G/D(G)` is Theorem 5.3.1, stated separately as `RelativeDerivedGroupStatement`.
The compatibility of `Z` with base change, mentioned in the proof, is not stated.
