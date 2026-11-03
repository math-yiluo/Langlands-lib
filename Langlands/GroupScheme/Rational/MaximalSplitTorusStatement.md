# Cocharacters lie in maximal split tori; conjugacy of maximal split tori of smooth groups

Authors: Worker 777 and Worker 1240.

This module defines two `Prop`-valued declarations in the namespace
`Langlands.GroupScheme`, each at an arbitrary universe `u`:

- `CocharacterMaximalSplitTorusStatement`: every cocharacter of an affine
  group scheme of finite type over a field factors through a maximal split
  torus;
- `SmoothMaximalSplitTorusConjugacyStatement`: in a smooth connected affine
  group over a field, any two maximal split tori are conjugate by a rational
  point.

The file contains no proof. It only defines these two propositions. Neither is
proved, assumed as an axiom or registered as an instance. The file asserts no
existence of maximal split tori. Existence appears only inside the conclusion
of `CocharacterMaximalSplitTorusStatement`, which is not asserted here.

The module imports `Langlands.GroupScheme.Rational.SplitTorus`,
`Langlands.GroupScheme.InnerAutomorphism` and
`Langlands.GroupScheme.Torus.Lattice`.

## Sources

- Conrad, Gabber and Prasad, *Pseudo-reductive groups*, second edition
  (2015), source ID `conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
  `1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
  Printed page = PDF page − 26.
  - Theorem C.2.3 (Borel–Tits), printed p.593 (PDF p.619): "Let G be a
    smooth connected affine group over a field k. All maximal k-split k-tori
    in G are G(k)-conjugate." The proof (printed pp.593–594, PDF pp.619–620)
    goes by induction on `dim G`, using Lemma C.2.2 and pseudo-parabolic
    subgroups. It places no condition on `k`.
  - Printed pp.594–595 (PDF pp.620–621), proof of Proposition C.2.4: "by
    Theorem C.2.3 applied to P we can replace λ with a suitable P(k)-conjugate
    to arrange that λ takes values in S". Here `P` is a pseudo-parabolic
    subgroup and `S` a maximal `k`-split `k`-torus of `P`. This use of
    Theorem C.2.3 for the non-reductive group `P` is the reason the second
    statement is formalized for smooth connected affine groups, not only for
    reductive ones.
- Milne, *Algebraic Groups* (2017), source ID `milne-2017-algebraic-groups`,
  SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
  Printed page = PDF page − 16.
  - Section 12.e, printed p.236 (PDF p.252): "A quotient of a split torus is
    again a split torus."
  - Definition 19.20, printed p.401 (PDF p.417): "The k-rank of G is the
    dimension of a maximal split torus in G".
  - The errata snapshot `milne-2017-algebraic-groups-errata-2026-11-02` has no
    entry for printed p.236 or p.401.

## Provenance of `CocharacterMaximalSplitTorusStatement`

`CocharacterMaximalSplitTorusStatement` is not a numbered theorem of these
sources. It is internal, derived content, stated for the proof of the
published `StandardParabolicClassificationStatement`, where it supplies the
step "λ takes values in a maximal split torus of `P`" that CGP use on
pp.594–595. The standard argument it records is the following.

1. The image of `χ : 𝔾ₘ ⟶ G` is a closed subgroup `H` of `G` that is a quotient
   of `𝔾ₘ`, so `H` is a split torus (Milne p.236), and `χ` factors through the
   closed immersion `H ⟶ G`.
2. Among the split subtori of `G` containing `H` (there is at least one, `H`
   itself), take one, `T`, of largest dimension. Dimensions of closed
   subgroups are bounded by `dim G`, which is finite because `G` is of finite
   type over `k`.
3. `T` is maximal. A split subtorus `T'` containing `T` also contains `H`, so
   `dim T' ≤ dim T`. Since `T'` is smooth and connected, `T = T'`.
4. `χ` factors as `𝔾ₘ ⟶ T ⟶ G`, and the first map is a cocharacter `ν` of `T`.

For the trivial cocharacter, `H` is trivial and the argument still produces a
maximal split torus.

## The statements

Throughout, `k : Type u` is a field and `S = Spec (CommRingCat.of k)`.

### `CocharacterMaximalSplitTorusStatement`

For every field `k : Type u`, every group scheme `G` over `S` whose structure
morphism `G.X.hom` is affine (`IsAffineHom`) and locally of finite type
(`LocallyOfFiniteType`), and every homomorphism
`χ : (Gm S).toGrp ⟶ G` of group schemes, there exist a commutative group
scheme `T` over `S`, a homomorphism `i : T.toGrp ⟶ G` and a cocharacter
`ν : cocharacterLattice T` (a homomorphism `Gm S ⟶ T` of commutative group
schemes) such that `IsMaximalSplitTorus i` and
`CommGroupScheme.groupHom ν ≫ i = χ`. Here `CommGroupScheme.groupHom ν` is
the underlying homomorphism `(Gm S).toGrp ⟶ T.toGrp`.

No smoothness, connectedness or reductivity of `G` is assumed. No
hypothesis is placed on `k`: it need not be perfect or algebraically closed,
and its characteristic is arbitrary. The trivial cocharacter is included.

### `SmoothMaximalSplitTorusConjugacyStatement`

For every field `k : Type u` and every group scheme `G` over `S` such that

- the structure morphism is smooth (`Smooth G.X.hom`) and affine
  (`IsAffineHom G.X.hom`), and
- the underlying scheme has connected underlying space
  (`ConnectedSpace G.X.left`),

the following holds. Let `T`, `T'` be commutative group schemes over `S` and
`i : T.toGrp ⟶ G`, `i' : T'.toGrp ⟶ G` homomorphisms with
`IsMaximalSplitTorus i` and `IsMaximalSplitTorus i'`. Then there exist a
rational point `g : Over.mk (𝟙 S) ⟶ G.X` (a point of `G(k)`) and an
isomorphism `e : T.toGrp ≅ T'.toGrp` of group schemes with
`i ≫ (G.innerIso g).hom = e.hom ≫ i'`.

No reductivity of `G` is assumed. No hypothesis is placed on `k`: it need not
be perfect or algebraically closed, and its characteristic is arbitrary.

## Definitions used

- `IsMaximalSplitTorus i` (module `Langlands.GroupScheme.Rational.SplitTorus`)
  holds when `i` is a split subtorus and every factorization `f ≫ i' = i`
  through a split subtorus `i'` has `f` an isomorphism. A split subtorus
  (`IsSplitSubtorus`) is a homomorphism whose source is a split torus
  (`IsSplitTorus`: isomorphic to `splitTorus S I = 𝔾ₘ^I` for a finite
  `I : Type u`) and which is a closed immersion (`IsClosedSubgroup`).
- `cocharacterLattice T` (module `Langlands.GroupScheme.Torus.Lattice`) is
  `Gm S ⟶ T`, the homomorphisms of commutative group schemes.
  `CommGroupScheme.groupHom` sends such a homomorphism to the underlying
  homomorphism of group schemes.
- `G.innerIso g` (module `Langlands.GroupScheme.InnerAutomorphism`) is the
  inner automorphism of `G` that sends every point `x` to `g x g⁻¹`, where `g`
  is pulled back to the test scheme.

## Departures from the sources

- **`CocharacterMaximalSplitTorusStatement` has no source counterpart.** It
  is derived, as explained above. Its hypotheses are those of an affine
  algebraic group in Milne's sense, a group scheme of finite type over `k`.
  An affine morphism is quasi-compact, so an affine morphism locally of
  finite type is of finite type. Smoothness and connectedness are not
  needed for the argument and are not assumed.
- **Subgroups as homomorphisms.** The sources speak of `k`-split `k`-tori as
  subgroups of `G`. Here a split torus of `G` is a closed-immersion
  homomorphism `i : T.toGrp ⟶ G` whose source `T` is a commutative group
  scheme isomorphic to some `𝔾ₘ^I`. Split tori are commutative, so requiring
  `T` to be commutative loses nothing. Inclusion of subgroups `S₁ ⊆ S₂` is a
  factorization `i₁ = f ≫ i₂`. A cocharacter "taking values in" a torus is the
  factorization `χ = groupHom ν ≫ i`. These renderings are choices of this
  formalization.
- **Maximality.** CGP's "maximal `k`-split `k`-torus" is maximal for inclusion
  among `k`-split `k`-tori of `G`. `IsMaximalSplitTorus i` says that `i` is
  not properly contained in another split subtorus: every factorization
  through a split subtorus is by an isomorphism.
- **Conjugacy.** CGP's `G(k)`-conjugacy, `g S g⁻¹ = S'` for some `g ∈ G(k)`,
  is expressed as `i ≫ (G.innerIso g).hom = e.hom ≫ i'`. Both sides are closed
  immersions, so the equation says that conjugating the image of `i` by `g`
  gives the image of `i'`, with `e` the induced isomorphism of sources. The
  choice between `g` and `g⁻¹` does not matter, because `G(k)` is a group.
  This rendering is a choice of this formalization. It is the conclusion form
  of the first part of the published `MaximalSplitTorusConjugacyStatement`
  (module `Langlands.GroupScheme.Rational.ConjugacyStatement`), whose
  hypothesis is `IsConnectedReductive G` instead.
- **Smooth connected affine group.** CGP's "smooth connected affine group
  over `k`" is an affine group scheme of finite type over `k` that is smooth
  and connected. It is rendered as `Smooth G.X.hom`, `IsAffineHom G.X.hom`
  and `ConnectedSpace G.X.left`. Finite type follows: smoothness gives
  locally of finite presentation, and affineness gives quasi-compactness.
- **Rank not included.** CGP's remark after Theorem C.2.3 (all maximal
  `k`-split tori have a common dimension, the `k`-rank) and Milne's
  Definition 19.20 are not part of `SmoothMaximalSplitTorusConjugacyStatement`.
  Only the conjugacy assertion is formalized here.
- **Universes.** The field is `k : Type u`, and split tori are indexed by
  finite types `I : Type u`. Both declarations are stated at an arbitrary
  universe `u`.
