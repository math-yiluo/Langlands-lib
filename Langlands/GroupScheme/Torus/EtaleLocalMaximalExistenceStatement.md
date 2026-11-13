# Statement: reductive group schemes have maximal tori étale-locally

Worker 75.

`Langlands.GroupScheme.EtaleLocalMaximalTorusExistenceStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports
[`Torus.FieldPointMaximality`](FieldPointMaximality.md) (for `IsFibrewiseMaximalTorus`)
and [`Torus.Relative`](Relative.md) (for `RelativeTorus.IsTorus`).

## Statement and quantifiers

The proposition quantifies over every scheme `S : Scheme.{u}` and every group scheme
`G : GroupScheme S`. It has one hypothesis: `IsReductive G`
([`Reductive.Basic`](../Reductive/Basic.md)). This says that `G` is smooth and affine over
`S` and that its geometric fibres are connected reductive groups.

The conclusion is that there is an étale cover
`𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S` of `S`. This is a family of étale
morphisms `𝒰.f j : 𝒰.X j ⟶ S`, indexed by `j : 𝒰.I₀`, whose images cover `S`. It is the
same kind of cover that `RelativeTorus.IsTorus` uses. For every index `j` there are a
commutative group scheme `T : CommGroupScheme (𝒰.X j)` and a homomorphism
`t : T.toGrp ⟶ (GroupScheme.baseChange (𝒰.f j)).obj G` into the base change of `G` to
`𝒰.X j` such that:

1. `RelativeTorus.IsTorus T.toGrp`: `T` becomes a split torus on some étale cover of
   `𝒰.X j`;
2. `IsClosedSubgroup t`: the underlying morphism of schemes of `t` is a closed immersion;
3. `IsFibrewiseMaximalTorus t`: for every point `x` of `𝒰.X j`, the residue fibre of `t`
   over `κ(x)` satisfies the field predicate `IsMaximalTorus`
   ([`Torus.Maximal`](Maximal.md)). In that fibre the torus is a closed subgroup and
   factors through no strictly larger closed `κ(x)`-torus of the fibre of `G`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
printed page numbers, which agree with the one-based PDF page numbers of this file.

- Corollary 3.2.7, p.95, first sentence: "Any reductive group scheme G → S admits a
  maximal torus étale-locally on S." The proof that follows takes sections of the smooth
  surjection `Tor_{G/S} → S` étale-locally on `S`.
- Definition 3.1.1, p.81, defines an `S`-torus as an `S`-group of multiplicative type with
  smooth connected fibres, and a reductive `S`-group as a smooth `S`-affine group whose
  geometric fibres are connected reductive groups.
- Definition 3.2.1, p.91: "A maximal torus in a smooth S-affine group scheme G → S is a
  torus T ⊂ G such that for each geometric point s̄ of S the fiber T_s̄ is not contained in
  any strictly larger torus in G_s̄."
- Remark A.1.2, p.267: over a field `k`, maximality of a `k`-torus in the geometric sense
  of Definition 3.2.1 is the same as maximality among `k`-tori.
- Proposition B.3.4, pp.290–291: a group of multiplicative type is diagonalizable
  étale-locally on the base.
- Lemma B.1.3, p.281: a monic homomorphism from a group of multiplicative type to an
  `S`-affine `S`-group of finite presentation is a closed immersion.

## Derivation from the source

"Étale-locally on `S`" is expressed by an étale cover of `S` and a maximal torus of `G`
over each member of the cover. Hypotheses 1–3 encode "maximal torus of `G_{U_j}`" in the
same way as the other relative maximal-torus statements in the Library:

- Property 1: an `S`-torus in the sense of Definition 3.1.1 is étale-locally split by
  Proposition B.3.4, because its fibres are smooth and connected and so its character
  sheaf is torsion-free. Conversely, an étale-locally split group is of multiplicative type
  with smooth connected fibres.
- Property 2: by Lemma B.1.3 a torus mapping monically to the affine finitely presented
  `G_{U_j}` is a closed subgroup, so requiring a closed immersion adds nothing.
- Property 3 states maximality on residue fibres rather than on geometric fibres. By
  Remark A.1.2 the two agree fibre by fibre, so `t` is a maximal torus in the sense of
  Definition 3.2.1.

## Scope

All objects are in universe `u`, and the base `S` is an arbitrary scheme. The proposition
covers only the first sentence of Corollary 3.2.7. The second sentence is about connected
reductive groups over a field, and the proposition does not state it. The torus over each
`U_j` need not be split over `U_j`, and the cover need not be finite.

## Relation to the Library

- [`Torus.StrictHenselianMaximalStatement`](StrictHenselianMaximalStatement.md) states a
  related existence result. Over a henselian local ring with separably closed residue
  field, it gives a split torus that is maximal on every residue fibre.
- [`Torus.MaximalTorusSchemeStatement`](MaximalTorusSchemeStatement.md) states the
  representability of the functor of maximal tori by a smooth surjective `S`-scheme, which
  is the source's route to this corollary.

This module proves none of these relations.
