# Statement: isomorphisms of reductive groups with split maximal tori and Borel subgroups

Worker 75.

`Langlands.GroupScheme.ReductiveSplitTorusBorelIsomorphismStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no other
definitions, theorems or axioms. It imports:

- Mathlib's `Mathlib.AlgebraicGeometry.Morphisms.Etale`, for `Etale`;
- [`AlgebraicGeometry.Picard.LineBundle`](../../AlgebraicGeometry/Picard/LineBundle.md), for
  `LineBundle` and `LineBundle.trivial`;
- [`RelativeLevi.Borel`](../RelativeLevi/Borel.md), for `IsRelativeBorelSubgroup`;
- [`Torus.FieldPointMaximality`](../Torus/FieldPointMaximality.md), for
  `IsFibrewiseMaximalTorus`;
- [`Torus.Lattice`](../Torus/Lattice.md), for `splitTorus.commGroupScheme`;
- [`InnerAutomorphism`](../InnerAutomorphism.md), for `GroupScheme.innerIso`.

`IsReductive`, `IsClosedSubgroup` ([`Reductive.Basic`](Basic.md)), `splitTorus`
([`Torus.Split`](../Torus/Split.md)), `SubgroupFunctor.range`
([`SubgroupFunctor`](../SubgroupFunctor.md)) and the base-change functor
`GroupScheme.baseChange` of [`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)
come transitively. `GroupScheme S` is `Grp (Over S)`, and an isomorphism `G ≅ G'` in it is
an isomorphism of group schemes over `S`.

## Predicates and constructions used

- `IsReductive G`: the structure morphism of `G` is smooth and affine, and every geometric
  fibre of `G` is a connected reductive group over an algebraically closed field (Conrad,
  Definition 3.1.1).
- `LineBundle S` is the full subcategory of sheaves of `𝒪_S`-modules that are locally free of
  rank one (`IsLocallyFreeRankOne`: every point has an open neighbourhood `U` on which the
  sheaf is isomorphic to `𝒪_U`). `LineBundle.trivial S` is `𝒪_S`. An isomorphism `L ≅ M` in
  `LineBundle S` is an isomorphism of the underlying module sheaves.
- `Scheme.precoverage @Etale` consists of the jointly surjective families of étale morphisms,
  that is, the étale coverings. `Scheme.Cover.{u} (Scheme.precoverage @Etale) S` is the type of
  such covers `𝒱` of `S`, with members `𝒱.f j : 𝒱.X j ⟶ S` indexed by `j : 𝒱.I₀` in universe
  `u`. The Library uses the same encoding of étale covers, for example in
  [`Reductive.FpqcLocalIsomorphismStatement`](FpqcLocalIsomorphismStatement.md).
- For `f : U ⟶ S`, `(GroupScheme.baseChange f).obj G` is the pullback `G_U` with its induced
  group law.
- `splitTorus S I`, for a finite type `I`, is the split torus `𝔾_m^I` over `S`, the finite
  product of copies of `𝔾_m`. `splitTorus.commGroupScheme S I` is the same group scheme as a
  commutative group scheme; it is the source of the predicate `IsFibrewiseMaximalTorus`.
- `IsClosedSubgroup t`: the underlying morphism of schemes of the homomorphism `t` is a closed
  immersion.
- `IsFibrewiseMaximalTorus t`: for every point `s` of `S`, the fibre of `t` over the residue
  field `κ(s)` satisfies `IsMaximalTorus`: its source is a torus, it is a closed subgroup, and
  it does not factor through a strictly larger closed torus over `κ(s)`.
- `IsRelativeBorelSubgroup i`, for `i : B ⟶ G`: the Library's transcription of Conrad's
  Definition 5.2.10. `i` is a parabolic subgroup over `S` (`IsRelativeParabolicSubgroup`)
  whose fibre over `κ(s)` is, for every point `s`, a Borel subgroup that stays Borel over an
  algebraic closure of `κ(s)`.
- `SubgroupFunctor.range f`, for a homomorphism `f : H ⟶ G`, assigns to every test scheme
  `T` over `S` the subgroup of points `T ⟶ G` that factor through `f`. For a closed subgroup it
  is the functor of points of the image. `≤` and `=` between such functors are inclusion and
  equality on every test scheme.
- `Over.mk (𝟙 S) ⟶ G.X` is a point `g ∈ G(S)`. `G.innerIso g : G ≅ G` is conjugation
  `x ↦ g x g⁻¹` on every test scheme (`GroupScheme.comp_innerIso_hom`). So
  `SubgroupFunctor.range (i ≫ (G.innerIso g).hom)` is the conjugate subgroup `g B g⁻¹`.

## Statement and quantifiers

The proposition quantifies over every scheme `S : Scheme.{u}` with hypotheses

- `ConnectedSpace S`: `S` is non-empty and connected;
- every `L : LineBundle S` is isomorphic to `LineBundle.trivial S`: `Pic(S) = 1`.

Its conclusion is the conjunction of two parts.

**Part 1 (pairs and triples).** For all `G G' : GroupScheme S` with `IsReductive G` and
`IsReductive G'` such that

- there is an étale cover `𝒱` of `S` with an isomorphism `G_{𝒱.X j} ≅ G'_{𝒱.X j}` of group
  schemes over `𝒱.X j` for every index `j`,

and for all finite types `I I' : Type u` and homomorphisms `t : splitTorus S I ⟶ G`,
`t' : splitTorus S I' ⟶ G'` with `IsClosedSubgroup t`, `IsFibrewiseMaximalTorus t`,
`IsClosedSubgroup t'` and `IsFibrewiseMaximalTorus t'`, write `T` and `T'` for the images of
`t` and `t'`. Then:

1. there is an isomorphism `Φ : G ≅ G'` with
   `SubgroupFunctor.range (t ≫ Φ.hom) = SubgroupFunctor.range t'`, that is, `Φ(T) = T'`;
2. for all group schemes `B B'` over `S` and homomorphisms `i : B ⟶ G`, `i' : B' ⟶ G'` with
   `IsRelativeBorelSubgroup i`, `IsRelativeBorelSubgroup i'`,
   `SubgroupFunctor.range t ≤ SubgroupFunctor.range i` (`T ⊆ B`) and
   `SubgroupFunctor.range t' ≤ SubgroupFunctor.range i'` (`T' ⊆ B'`), there is an
   isomorphism `Φ : G ≅ G'` with `Φ(T) = T'` and
   `SubgroupFunctor.range (i ≫ Φ.hom) = SubgroupFunctor.range i'`, that is, `Φ(B) = B'`.

**Part 2 (conjugacy over an affine base).** If moreover `IsAffine S`, then for every
`G : GroupScheme S` with `IsReductive G`, all finite types `I I' : Type u` and homomorphisms
`t : splitTorus S I ⟶ G`, `t' : splitTorus S I' ⟶ G` with the same four hypotheses (closed
subgroups that are maximal tori on residue fibres):

1. there is `g ∈ G(S)` with
   `SubgroupFunctor.range (t ≫ (G.innerIso g).hom) = SubgroupFunctor.range t'`, that is,
   `g T g⁻¹ = T'`;
2. for all Borel subgroups `i : B ⟶ G`, `i' : B' ⟶ G` with `T ⊆ B` and `T' ⊆ B'` (the same
   hypotheses as in Part 1 with `G' = G`), there is `g ∈ G(S)` with `g T g⁻¹ = T'` and
   `g B g⁻¹ = B'`.

The isomorphisms and points are only asserted to exist. They are not required to be
compatible with the given parametrizations `t`, `t'` of the tori or with the étale-local
isomorphisms.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
one-based PDF pages, which agree with the printed page numbers.

- Proposition 6.2.11, p.210: "Let G and G′ be reductive groups over a non-empty scheme S. …
  2. Assume that G and G′ are isomorphic étale-locally on S, that S is connected with
  Pic(S) = 1, and that G and G′ have respective split maximal tori T and T′. The pairs (G, T)
  and (G′, T′) are isomorphic, as are the triples (G, B, T) and (G′, B′, T′) for Borel
  subgroups B ⊃ T and B′ ⊃ T′. If G′ = G and S is also affine (so H¹(S, O_S) = 0) then these
  isomorphisms can be chosen to arise from G(S)-conjugation."
- Proof of (2), pp.210–211. Since `S` is connected, the character groups of `T` and `T′` are
  constant, and since `Pic(S) = 1` the root spaces are free of rank one, so `(G, T)` and
  `(G′, T′)` are split and Borel subgroups containing `T` and `T′` exist. They correspond to
  positive systems of roots, and the full faithfulness of (6.1.2) gives an isomorphism of
  triples. For `G′ = G` over affine `S`: `B` is a successive extension of copies of `𝔾_a` and
  `𝔾_m`, and `H¹(S_ét, 𝔾_a) = H¹(S, 𝒪_S) = 0` (affine) and `H¹(S_ét, 𝔾_m) = Pic(S) = 1` give
  `H¹(S_ét, B) = 1`, so `G(S)` acts transitively on the Borel subgroups (via
  `Bor_{G/S} ≅ G/B`, Corollaries 5.2.7 and 5.2.8). Two split maximal tori in `B` are
  `B(S)`-conjugate, because their transporter is an étale torsor under `N_B(T) = T ≅ 𝔾_m^r`,
  which is trivial since `Pic(S) = 1`.
- Definition 3.2.1, p.91 (maximal tori via geometric fibres); Remark A.1.2, p.267 (geometric
  maximality agrees with maximality among tori over a field); Lemma B.1.3, p.281 (a monic
  homomorphism from a group of multiplicative type to an affine finitely presented group is a
  closed immersion).
- Definition 5.2.10, p.157 (Borel subgroups over a base), transcribed by
  `IsRelativeBorelSubgroup`.

## Derivation from the source

The proposition is a transcription of Proposition 6.2.11(2), with the following encodings.

- **Reductive groups.** Conrad's reductive groups over `S` are `IsReductive`.
- **"S connected" and non-empty.** Mathlib's `ConnectedSpace` includes non-emptiness, which is
  Conrad's standing assumption in Proposition 6.2.11.
- **"Pic(S) = 1".** `Pic(S)` is the group of isomorphism classes of invertible sheaves on `S`,
  which are the locally free sheaves of rank one. It is trivial exactly when every such sheaf
  is isomorphic to `𝒪_S`, which is the hypothesis on `LineBundle S`.
- **"Isomorphic étale-locally on S".** There is an étale covering family of `S` over each
  member of which the two groups become isomorphic, encoded as in
  [`Reductive.FpqcLocalIsomorphismStatement`](FpqcLocalIsomorphismStatement.md). Indexing the
  cover in universe `u` loses nothing.
- **"Split maximal torus".** A split torus is `D_S(M)` for a finite free `ℤ`-module `M`; a
  basis gives `D_S(M) ≅ 𝔾_m^I = splitTorus S I`. A maximal torus of `G` is a torus subgroup
  that is a maximal torus on geometric fibres. It is given by its inclusion `t`, which is a
  closed immersion (Lemma B.1.3), and maximality on residue fibres agrees with geometric
  maximality (Remark A.1.2). This is the encoding of the Library's other relative statements,
  for example [`Reductive.EtaleLocalSplitStatement`](EtaleLocalSplitStatement.md). A split
  maximal torus in Conrad's sense is only required to be split as a torus; no splitting of
  `(G, T)` in the sense of Definition 5.1.1 is assumed.
- **"The pairs (G, T) and (G′, T′) are isomorphic".** There is an isomorphism of group schemes
  `G ≅ G'` carrying `T` onto `T'`. Subgroups are compared through their functors of points,
  `SubgroupFunctor.range`, as in the other statements of this directory.
- **"Borel subgroups B ⊃ T".** Borel subgroups are given as abstract group schemes with
  homomorphisms into `G` satisfying `IsRelativeBorelSubgroup`, and containment is inclusion of
  functors of points. The triples statement is asserted for every such `B` and `B'`.
- **"Chosen to arise from G(S)-conjugation".** For `G′ = G`, the isomorphism is the inner
  automorphism `innerIso g` for some `g ∈ G(S)`. When `G′ = G` the étale-local isomorphism
  hypothesis holds trivially, so Part 2 omits it.
- **"(so H¹(S, O_S) = 0)".** This parenthetical records a consequence of affineness used in the
  proof, not an extra hypothesis, so it is not encoded.

## Scope

All schemes and index types are in universe `u`. The tori `T` and `T'` may a priori have
different ranks `I` and `I'`; under the hypotheses they have the same rank. No pinning, root
datum or positive system is given; these appear only in the source's proof.

## Not stated

The statement does not assert Proposition 6.2.11(1), which is
[`Reductive.FpqcLocalIsomorphismStatement`](FpqcLocalIsomorphismStatement.md). It does not
state the full faithfulness of (6.1.2), the vanishing `H¹(S_ét, B) = 1`, the identification
`Bor_{G/S} ≅ G/B`, or the equality `N_B(T) = T` used in the proof.

## Relation to the Library

- [`RelativeLevi.SplitBorelConjugacyStatement`](../RelativeLevi/SplitBorelConjugacyStatement.md)
  states Corollary 5.2.13, Zariski-local conjugacy of Borel subgroups of a split group.
- [`RelativeLevi.BorelConjugacyStatement`](../RelativeLevi/BorelConjugacyStatement.md) states
  Theorem 5.2.11(2), étale-local conjugacy of Borel subgroups.

This module proves none of these relations.
