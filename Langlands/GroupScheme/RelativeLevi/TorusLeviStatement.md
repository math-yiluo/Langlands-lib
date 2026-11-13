# Statement: the Levi subgroup containing a maximal torus

Worker 75.

`Langlands.GroupScheme.RelativeTorusLeviStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports [`RelativeLevi.Basic`](Basic.md) (for
`IsRelativeParabolicSubgroup` and `IsRelativeLeviSubgroup`),
[`Torus.FieldPointMaximality`](../Torus/FieldPointMaximality.md) (for
`IsFibrewiseMaximalTorus`) and [`Torus.Relative`](../Torus/Relative.md) (for
`RelativeTorus.IsTorus`).

## Statement and quantifiers

The proposition quantifies over:

- every scheme `S : Scheme.{u}`;
- every pair of group schemes `G P : GroupScheme S` and homomorphism `i : P ⟶ G`;
- every commutative group scheme `T : CommGroupScheme S` and homomorphism
  `t : T.toGrp ⟶ P`.

It has five hypotheses:

1. `IsReductive G` ([`Reductive.Basic`](../Reductive/Basic.md)): `G` is smooth and affine
   over `S` with connected reductive geometric fibres.
2. `IsRelativeParabolicSubgroup i` ([`RelativeLevi.Basic`](Basic.md)).
3. `RelativeTorus.IsTorus T.toGrp`: there is an étale cover of `S` over each member of
   which `T` becomes a split torus.
4. `IsClosedSubgroup t`: the underlying morphism of schemes `T ⟶ P` is a closed immersion.
5. `IsFibrewiseMaximalTorus t`: for every point `s` of `S`, the residue fibre
   `t_s : T_s ⟶ P_s` over `κ(s)` satisfies the field predicate `IsMaximalTorus`
   ([`Torus.Maximal`](../Torus/Maximal.md)): `T_s` is a torus, `t_s` is a closed subgroup,
   and `t_s` factors through no strictly larger closed `κ(s)`-torus of `P_s`.

The conclusion: there are `L : GroupScheme S` and `l : L ⟶ P` such that

- `IsRelativeLeviSubgroup l`;
- `SubgroupFunctor.range t ≤ SubgroupFunctor.range l`: on every test scheme, every point
  of `P` that factors through `t` factors through `l`, so `T` lies in `L`;
- for every `L' : GroupScheme S` and `l' : L' ⟶ P` with `IsRelativeLeviSubgroup l'` and
  `SubgroupFunctor.range t ≤ SubgroupFunctor.range l'`, the images agree:
  `SubgroupFunctor.range l' = SubgroupFunctor.range l`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014; registered as `conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
one-based PDF pages, which agree with the printed page numbers of this file.

- Proposition 5.4.5, p.177: "For every maximal torus T ⊂ P there is a unique Levi
  S-subgroup L ⊂ P containing T." The ambient setting is that of Definition 5.4.2, p.174:
  `G → S` is a reductive group scheme and `P ⊂ G` a parabolic subgroup.
- Definition 3.1.1, p.81: "An S-torus is an S-group T → S of multiplicative type with
  smooth connected fibers."
- Definition 3.2.1, p.91: "A maximal torus in a smooth S-affine group scheme G → S is a
  torus T ⊂ G such that for each geometric point s̄ of S the fiber T_s̄ is not contained in
  any strictly larger torus in G_s̄."
- Remark A.1.2, p.267: over a field `k`, maximality of a `k`-torus in the geometric sense of
  Definition 3.2.1 is the same as maximality among `k`-tori.
- Proposition B.3.4, pp.290–291: a group of multiplicative type is diagonalizable
  étale-locally on `S`.
- Lemma B.1.3, p.281: a monic homomorphism from a group of multiplicative type to an
  `S`-affine `S`-group of finite presentation is a closed immersion.

## Derivation from the source

The proposition is Proposition 5.4.5 with "unique" expressed as equality of images on
every test scheme, as in the other statements of this directory: two Levi subgroups are
given as abstract group schemes with closed immersions into `P`, and they are the same
subgroup exactly when their images agree as subgroup functors.

The maximal torus `T ⊂ P` of the source is encoded by hypotheses 3–5.

- Hypothesis 3: an `S`-torus in the sense of Definition 3.1.1 is étale-locally split by
  Proposition B.3.4 (its fibres are connected and smooth, so the character sheaf is
  torsion-free), and conversely an étale-locally split group is of multiplicative type with
  smooth connected fibres. The Library's `RelativeTorus.IsTorus` is this étale-local
  splitting.
- Hypothesis 4: the source's `T ⊂ P` is a subgroup; by Lemma B.1.3 a torus mapping
  monically to the affine finitely presented `P` is closed, so requiring a closed
  immersion adds nothing.
- Hypothesis 5 states maximality on residue fibres, through the Library's existing
  predicate `IsFibrewiseMaximalTorus`, rather than on geometric fibres. By Remark A.1.2
  the two agree fibre by fibre, so `t` is a maximal torus of `P` in the sense of
  Definition 3.2.1.

## Scope

All objects are in universe `u`. The base `S` is an arbitrary scheme. `T` need not be
split over `S`, and no cocharacter is given. The torus is required to be maximal in `P`,
as in the source; since a parabolic subgroup contains a maximal torus of `G` on every
geometric fibre, this is the same as a maximal torus of `G` lying in `P`, but the
proposition does not use that comparison.

## Relation to the Library

- `IsFibrewiseMaximalTorus` is the maximal-torus hypothesis already used over a base in
  the published `Reductive.LocalWeylNormalizationStatement`
  ([`Reductive.LocalWeylNormalizationStatement`](../Reductive/LocalWeylNormalizationStatement.md)).
- `RelativeLeviConjugacyStatement` ([`ConjugacyStatement`](ConjugacyStatement.md)), in
  this directory, transcribes Corollary 5.4.6, which the source deduces from this
  proposition.

This module proves none of these relations.
