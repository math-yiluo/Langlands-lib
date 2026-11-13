# Statement: maximal tori are conjugate étale-locally on the base

Worker 75.

`Langlands.GroupScheme.EtaleLocalMaximalTorusConjugacyStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports
[`Torus.FieldPointMaximality`](FieldPointMaximality.md) (for `IsFibrewiseMaximalTorus`),
[`Torus.Relative`](Relative.md) (for `RelativeTorus.IsTorus`) and
[`InnerAutomorphism`](../InnerAutomorphism.md) (for `GroupScheme.innerIso`).

## Statement and quantifiers

The proposition quantifies over:

- every scheme `S : Scheme.{u}`;
- every group scheme `G : GroupScheme S` with instances `Smooth G.X.hom` and
  `IsAffineHom G.X.hom` (the structure morphism of `G` is smooth and affine);
- every pair of commutative group schemes `T T' : CommGroupScheme S` with homomorphisms
  `t : T.toGrp ⟶ G` and `t' : T'.toGrp ⟶ G`.

It has six hypotheses, three for each of `t` and `t'`:

1. `RelativeTorus.IsTorus T.toGrp` and `RelativeTorus.IsTorus T'.toGrp`: each of `T` and
   `T'` becomes a split torus on some étale cover of `S`.
2. `IsClosedSubgroup t` and `IsClosedSubgroup t'`: the underlying morphisms of schemes are
   closed immersions.
3. `IsFibrewiseMaximalTorus t` and `IsFibrewiseMaximalTorus t'`: for every point `s` of
   `S`, the residue fibre over `κ(s)` satisfies the field predicate `IsMaximalTorus`
   ([`Torus.Maximal`](Maximal.md)). In that fibre the torus is a closed subgroup and
   factors through no strictly larger closed `κ(s)`-torus of `G_s`.

The conclusion is that there is an étale cover
`𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S` of `S`. This is a family of étale
morphisms `𝒰.f j : 𝒰.X j ⟶ S` whose images cover `S`. For every index `j` there is a point
`g : Over.mk (𝟙 (𝒰.X j)) ⟶ ((GroupScheme.baseChange (𝒰.f j)).obj G).X`, that is, a
point `g ∈ G(U_j)` with `U_j = 𝒰.X j`, such that

`SubgroupFunctor.range (t_{U_j} ≫ (innerIso g).hom) = SubgroupFunctor.range t'_{U_j}`.

Here `t_{U_j}` and `t'_{U_j}` are the base changes
`(GroupScheme.baseChange (𝒰.f j)).map t` and `.map t'`, and `innerIso g` is the inner
automorphism `x ↦ g x g⁻¹` of `G_{U_j}`. The equality says that on every test scheme over
`U_j`, the points of `g T_{U_j} g⁻¹` are exactly the points of `T'_{U_j}`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
printed page numbers, which agree with the one-based PDF page numbers of this file.

- Theorem 3.2.6, p.94. Its hypothesis is that `G → S` is a smooth `S`-affine group scheme
  such that, in the identity component of each geometric fibre, the maximal tori are their
  own centralizers. Its last two sentences are: "If T is a maximal torus of G then the map
  G/N_G(T) → Tor_{G/S} defined by G-conjugation against T is an isomorphism. In
  particular, any two maximal tori of G are conjugate étale-locally on S."
- The proof of Theorem 3.2.6, pp.94–95. It first uses the centralizer hypothesis to
  produce, fppf-locally and then Zariski-locally around each point, a torus `T` that is
  maximal in `G`. It then says: "Now we will just use that G → S is a smooth S-affine
  group." It shows that `G/N_G(T)`
  is a subfunctor of `Tor_{G/S}` and reduces the equality to the claim that "any two
  maximal tori T and T′ in G are conjugate fppf-locally on S". It proves that claim by
  direct limits (Lemma 3.2.5), Artin approximation and Corollary B.3.5.
- Theorem 2.3.1, p.67: for a smooth `S`-affine group `G` and a subgroup `H` of
  multiplicative type, `G/N_G(H)` exists as a smooth quasi-affine `S`-scheme. Remark 2.3.5,
  p.71: "The quotient maps G → G/Z_G(H) and G → G/N_G(H) are smooth since Z_G(H) and
  N_G(H) are smooth."
- Definition 3.1.1, p.81 (tori), and Definition 3.2.1, p.91 (maximal tori in a smooth
  `S`-affine group, tested on geometric fibres).
- Remark A.1.2, p.267: over a field `k`, maximality of a `k`-torus in the geometric sense
  of Definition 3.2.1 is the same as maximality among `k`-tori.
- Proposition B.3.4, pp.290–291: a group of multiplicative type is diagonalizable
  étale-locally on the base.
- Lemma B.1.3, p.281: a monic homomorphism from a group of multiplicative type to an
  `S`-affine `S`-group of finite presentation is a closed immersion.

## Derivation from the source

The proposition is the last sentence of Theorem 3.2.6 with the two maximal tori supplied.
The centralizer hypothesis of Theorem 3.2.6 is omitted, and only "smooth `S`-affine" is
kept. This follows the proof quoted above. Once the maximal torus `T` is given, the proof
uses only that `G → S` is smooth and `S`-affine:

- the identification of `G/N_G(T)` with `Tor_{G/S}` as fppf sheaves comes from the
  fppf-local conjugacy of any two maximal tori, which is proved for smooth `S`-affine `G`;
- the quotient map `G → G/N_G(T)` is a smooth surjection (Theorem 2.3.1 and Remark 2.3.5).
  So the point of `Tor_{G/S}(S)` given by `T'` lifts to `G` étale-locally on `S`, and any
  such lift `g` satisfies `g T g⁻¹ = T'`.

Reductive group schemes satisfy the centralizer hypothesis, so they are a special case.
They are the case of main interest in the source.

"Conjugate étale-locally on `S`" is expressed by an étale cover of `S` and, over each
member `U_j`, a point `g ∈ G(U_j)` carrying `T_{U_j}` onto `T'_{U_j}`. Two subgroups are
compared by equality of their images on every test scheme.

The maximal tori of the source are encoded by hypotheses 1–3:

- Hypothesis 1: an `S`-torus in the sense of Definition 3.1.1 is étale-locally split by
  Proposition B.3.4, and conversely an étale-locally split group is of multiplicative type
  with smooth connected fibres.
- Hypothesis 2: by Lemma B.1.3 a torus mapping monically to `G` is a closed subgroup, so
  requiring a closed immersion adds nothing.
- Hypothesis 3 states maximality on residue fibres rather than on geometric fibres. By
  Remark A.1.2 the two agree fibre by fibre, so each of `t` and `t'` is a maximal torus in
  the sense of Definition 3.2.1.

## Scope

All objects are in universe `u`, and the base `S` is an arbitrary scheme. `G` need not
have connected fibres and need not be reductive. The tori need not be split, and `T` and
`T'` are not assumed to be isomorphic. The proposition does not state the isomorphism
`G/N_G(T) ≅ Tor_{G/S}`, and it states nothing about the representability of `Tor_{G/S}`.

## Relation to the Library

- [`Torus.MaximalTorusSchemeStatement`](MaximalTorusSchemeStatement.md) states the first
  assertion of Theorem 3.2.6 for reductive group schemes.
- [`Torus.EtaleLocalMaximalExistenceStatement`](EtaleLocalMaximalExistenceStatement.md)
  states Corollary 3.2.7, the étale-local existence of maximal tori.
- Over an affine base `Spec R`, the Library's
  [`Torus.RelativeTransporterEtaleLift`](RelativeTransporterEtaleLift.md) and
  [`Torus.IdentityTransporterEtaleLift`](IdentityTransporterEtaleLift.md) construct
  étale neighbourhoods carrying transporter points between two homomorphisms from a
  diagonalizable group into `G`. They start from a transporter point over a field above
  a base point.

This module proves none of these relations.
