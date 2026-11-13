# Statement: Borel subgroups are conjugate étale-locally on the base

Worker 75.

`Langlands.GroupScheme.RelativeBorelEtaleLocalConjugacyStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports [`RelativeLevi.Borel`](Borel.md), for
`IsRelativeBorelSubgroup`, [`InnerAutomorphism`](../InnerAutomorphism.md), for
`GroupScheme.innerIso`, and Mathlib's `AlgebraicGeometry.Morphisms.Etale`, for `Etale`
and the étale precoverage.

## Statement and quantifiers

The proposition quantifies over:

- every scheme `S : Scheme.{u}`;
- group schemes `G B B' : GroupScheme S`;
- homomorphisms `i : B ⟶ G` and `i' : B' ⟶ G`.

It has three hypotheses:

1. `IsReductive G` ([`Reductive.Basic`](../Reductive/Basic.md)): `G` is smooth and
   affine over `S`, and its geometric fibres are connected reductive groups.
2. `IsRelativeBorelSubgroup i` ([`RelativeLevi.Borel`](Borel.md)): `i` is a parabolic
   subgroup in the sense of `IsRelativeParabolicSubgroup` (`B` is smooth and affine over
   `S`, `i` is a monomorphism of `S`-schemes, and every residue fibre of `i` is a
   parabolic subgroup), and for every point `s` of `S` the residue fibre
   `i_s : B_s ⟶ G_s` over `κ(s)` satisfies `IsGeometricBorelSubgroup`: it is a Borel
   subgroup over `κ(s)` whose base change to an algebraic closure of `κ(s)` is again a
   Borel subgroup.
3. `IsRelativeBorelSubgroup i'`, the same for `i'`.

The conclusion is that there is an étale cover
`𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S` of `S`. This is a family of étale
morphisms `𝒰.f j : 𝒰.X j ⟶ S` whose images cover `S`. For every index `j` there is a
point `g : Over.mk (𝟙 (𝒰.X j)) ⟶ ((GroupScheme.baseChange (𝒰.f j)).obj G).X`, that is,
a point `g ∈ G(U_j)` with `U_j = 𝒰.X j`, such that

    SubgroupFunctor.range (i_{U_j} ≫ (innerIso g).hom) = SubgroupFunctor.range i'_{U_j}.

Here `i_{U_j}` and `i'_{U_j}` are the base changes `(GroupScheme.baseChange (𝒰.f j)).map i`
and `.map i'`, and `innerIso g` is the inner automorphism `x ↦ g x g⁻¹` of `G_{U_j}`.
The equality says that on every test scheme over `U_j`, the points of `g B_{U_j} g⁻¹`
are exactly the points of `B'_{U_j}`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the one-based PDF pages, which agree with the printed page numbers.

- Theorem 5.2.11, p.157: "Let G → S be a reductive group scheme. [...] 2. Any two Borel
  subgroups of G are conjugate étale-locally on S."
- Proof of Theorem 5.2.11, p.158: "Part (2) follows from Corollary 5.2.7."
- Definition 5.2.10, p.157: "A Borel subgroup of a reductive group scheme G → S is a
  parabolic subgroup P ⊂ G such that P_s is a Borel subgroup of G_s for all s ∈ S."
- Corollary 5.2.7(1), p.155: parabolic subgroups `P`, `Q` with `P_s` conjugate to `Q_s`
  are `G(U)`-conjugate over an étale neighbourhood `U` of `(S, s)`.

## Derivation from the source

The proposition is Theorem 5.2.11(2), with its terms translated as follows.

- **"Borel subgroups of G".** Hypotheses 2 and 3 use the published predicate
  `IsRelativeBorelSubgroup`, the Library's transcription of Definition 5.2.10. Its
  module [`RelativeLevi.Borel`](Borel.md) explains why the fibres are required to be
  Borel subgroups after base change to an algebraic closure.
- **"Conjugate étale-locally on S".** This is expressed by an étale cover of `S` and,
  over each member `U_j`, a point `g ∈ G(U_j)` carrying `B_{U_j}` onto `B'_{U_j}`. The
  encoding is the one of the published
  [`Torus.EtaleLocalMaximalConjugacyStatement`](../Torus/EtaleLocalMaximalConjugacyStatement.md),
  which transcribes the same phrase for maximal tori. The proof in the source
  produces, for each point `s`, an étale neighbourhood of `(S, s)` by Corollary
  5.2.7(1). Étale morphisms are open, so these neighbourhoods together form an étale
  cover, and conversely each member of an étale cover is an étale neighbourhood of the
  points in its image.
- **Comparison of subgroups.** Subgroups are compared through their images as subgroup
  functors (`SubgroupFunctor.range`), the convention of the relative Levi statements of
  the Library. Because `i` and `i'` are monomorphisms, this is equality of the subgroups
  `g B_{U_j} g⁻¹` and `B'_{U_j}` of `G_{U_j}`.

## Scope

All objects are in universe `u`. The base `S` is an arbitrary scheme: it need not be
affine, Noetherian, reduced or connected, and the empty scheme is allowed. No maximal
torus, splitting or cocharacter over `S` is assumed, and `B`, `B'` are not assumed
isomorphic as abstract group schemes.

## Not stated

- Theorem 5.2.11(1), the open and closed Borel locus, is the published
  [`BorelLocusStatement`](BorelLocusStatement.md).
- Theorem 5.2.11(3), representability of the functor of Borel subgroups by a smooth
  proper `S`-scheme `Bor_{G/S}` with an ample line bundle, is not stated.

This module proves none of these assertions.
