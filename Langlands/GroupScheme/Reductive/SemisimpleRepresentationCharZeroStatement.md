# Reductive groups in characteristic zero and semisimple representations

`Langlands.GroupScheme.CharZeroReductiveSemisimpleRepresentationStatement.{u}`
is a Prop-valued definition. This module defines the proposition and proves
nothing.

## Statement

The proposition says: for every field `k : Type u` with `[CharZero k]` and
every group scheme `G : GroupScheme (Spec (CommRingCat.of k))` whose structure
morphism is locally of finite type and affine, if `ConnectedSpace G.X.left`,
then

```text
(IsConnectedReductive G ↔
    ∀ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)), IsSemisimpleRep n ρ) ∧
  (IsConnectedReductive G ↔
    ∃ (n : ℕ) (ρ : MatrixRepresentation G (Fin n)),
      IsClosedSubgroup ρ ∧ IsSemisimpleRep n ρ)
```

where `IsSemisimpleRep` is a local abbreviation inside the statement:

```text
IsSemisimpleRep n ρ :=
  sSup {W : Submodule k (Fin n → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
    ∀ U : Submodule k (Fin n → k), ρ.IsStableSubspace U → U ≤ W →
      U = ⊥ ∨ U = W} = ⊤
```

In words: let `G` be a connected affine algebraic group over a field of
characteristic zero. Then the following are equivalent:

- (a) `G` is reductive;
- (b) every finite-dimensional representation of `G` is semisimple;
- (c) some faithful finite-dimensional representation of `G` is semisimple.

The first conjunct is (a) ⇔ (b), the second is (a) ⇔ (c).

Every ingredient is an existing declaration, used without change:

- `MatrixRepresentation G (Fin n)` (from
  [`MatrixRepresentation`](../MatrixRepresentation.md)) is a homomorphism of
  group schemes `ρ : G ⟶ GL_n` over `k`, that is, a representation of `G` on
  `kⁿ` with its standard basis. Every finite-dimensional representation is
  isomorphic to one of these, so quantifying over all `n` and all `ρ` covers
  all finite-dimensional representations.
- `ρ.IsStableSubspace W` (from
  [`MatrixRepresentation.StableSubrepresentation`](../MatrixRepresentation/StableSubrepresentation.md))
  says: for every commutative `k`-algebra `A`, every point `x` of `G` with
  values in `A`, every `v ∈ W` and every `k`-linear map `ℓ : A → k`, applying
  `ℓ` to the coordinates of `ρ(x)v` gives a vector of `W`. Since `W ⊗ A` is the
  set of vectors of `Aⁿ` all of whose images under such `ℓ` lie in `W`, this
  says that `ρ(x)(W ⊗ A) ⊆ W ⊗ A` for all `A` and `x`. Applying it to `x⁻¹`
  gives equality. So the stable subspaces are exactly the subspaces stable
  under `G` in Milne's sense, that is, the subrepresentations (see the
  provenance below).
- The set inside `sSup` is the set of simple subrepresentations of `ρ`:
  nonzero stable subspaces `W` whose only stable subspaces contained in `W`
  are `0` and `W`. A subrepresentation of the representation on `W` is the same
  as a stable subspace of `kⁿ` contained in `W`. So `IsSemisimpleRep n ρ` says
  that `kⁿ` is the sum of the simple subrepresentations of `ρ`. For `n = 0`
  the condition holds trivially.
- `IsClosedSubgroup ρ` (from [`Reductive.Basic`](Basic.md)) says that the
  morphism of schemes underlying `ρ` is a closed immersion. This is how the
  Library's `AffineLinearEmbeddingStatement` expresses a faithful
  representation.
- `IsConnectedReductive G` (from [`Reductive.Basic`](Basic.md)) says that `G`
  is smooth, affine and connected, and that every smooth connected unipotent
  normal closed subgroup of the base change of `G` to `AlgebraicClosure k` is
  trivial (`HasTrivialUnipotentRadical`).
- `ConnectedSpace G.X.left` says that the underlying topological space of `G`
  is connected.

The hypotheses do not include smoothness of `G`. In characteristic zero it is
automatic (Cartier's theorem, see below), so all three conditions are about
the same groups as in Milne.

The Library already contains the related
`ReductiveCharZeroSemisimplicityStatement`
(`Reductive/CharZeroSemisimplicityStatement`). It assumes `k` algebraically
closed and `IsPseudoReductive G`, and concludes that the action of the group
of `k`-points on `kⁿ` is semisimple as an abstract representation. That is a
form of (a) ⇒ (b) only. The present statement works over every field of
characteristic zero, uses the subrepresentations of the group scheme, and
includes both converses.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

The statement is Theorem 22.42, printed p. 477 (PDF p. 493): "The following
conditions on a connected algebraic group G over k (of characteristic zero) are
equivalent: (a) G is reductive; (b) every finite-dimensional representation of
G is semisimple; (c) some faithful finite-dimensional representation of G is
semisimple." It is in Section 22c, which begins on printed p. 475 (PDF p. 491)
with "In this section, k is a field of characteristic zero."

The surrounding conventions are:

- Algebraic groups. "An algebraic group over k is a group object in the
  category of algebraic schemes over k", and "an algebraic k-scheme is a
  scheme of finite type over k" (printed p. 6, PDF p. 22). The notation
  section, printed p. 4 (PDF p. 20), says "After p. 162, all algebraic groups
  are affine." The Lean statement therefore assumes that `G` is affine and
  locally of finite type (hence of finite type, as an affine morphism is
  quasi-compact).
- Smoothness. Printed p. 13 (PDF p. 29): "In characteristic zero, all
  algebraic groups are smooth (3.23, 8.39 below)." Theorem 3.23 (Cartier),
  printed p. 71 (PDF p. 87): "Every affine algebraic group over a field of
  characteristic zero is smooth."
- Reductive. Printed p. 400 (PDF p. 416): "Recall (6.46) that an algebraic
  group G over a field k is said to be reductive if it is smooth and connected
  and the unipotent radical of G_{k^a} is trivial." This is
  `IsConnectedReductive`.
- Representations. Chapter 4 opens, printed p. 83 (PDF p. 99), with
  "Throughout this chapter, G is an affine algebraic group over a field k." On
  the same page: "A linear representation r is faithful if r(R): G(R) →
  Aut_{R-linear}(V_R) is injective for all k-algebras R. For finite-dimensional
  linear representations, this is equivalent to r being a closed immersion
  (3.35)." Chapter 22 opens, printed p. 463 (PDF p. 479), with "Throughout,
  representations are finite-dimensional unless it is specified otherwise."
- Subrepresentations. Proposition 4.3, printed p. 85 (PDF p. 101), defines the
  stabilizer `G_W` of a subspace `W` by the functor `R ⇝ {g ∈ G(R) | g(W_R) =
  W_R}`. The proof of Corollary 4.8, printed p. 86 (PDF p. 102), states: "A
  subspace W of V is stable under G if and only if it is an O(G)-subcomodule
  of V". These subspaces are the subrepresentations.
- Semisimple. Definition 4.15, printed p. 90 (PDF p. 106): "A representation
  of an algebraic group is simple if it is ≠ 0 and its only subrepresentations
  are 0 and itself. It is semisimple if it is a sum of simple
  subrepresentations." `IsSemisimpleRep` is this definition for the
  representation `ρ` on `kⁿ`. Proposition 4.17 and the paragraph after it
  (same page) show that this is equivalent to every subrepresentation being a
  direct summand.

The provenance is derived for these reasons:

- Milne lists three equivalent conditions. The Lean statement gives the two
  equivalences (a) ⇔ (b) and (a) ⇔ (c), which together are the theorem.
- Finite-dimensional representations are given in coordinates, as
  homomorphisms to `GL_n` on `kⁿ`, and faithfulness is expressed by the closed
  immersion condition, which Milne states is equivalent (3.35).
- Smoothness is not a hypothesis; it is part of (a) through
  `IsConnectedReductive`, and it holds for every `G` considered by Cartier's
  theorem 3.23.
- `k` and `G` lie in an arbitrary universe `u`, and the test algebras in
  `IsStableSubspace` lie in the same universe. This is a formalization
  convention. The universal point of `G`, with values in its coordinate ring,
  is one of these tests, so stability is the subcomodule condition.

Errata. The official errata snapshot of 2026-11-02 for the 2017 book (source
ID `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) lists, for
Chapter 1, a note that Notation 3.2 should be placed earlier and corrections
on pp. 18, 20, 21 and 26; under the heading Chapter 3, corrections on p. 80
(3.52) and p. 85, the latter reading "G_W is the stabilizer of W in G (not
V)", a wording correction to the sentence naming the stabilizer after
Proposition 4.3; for Chapter 4, only a correction on p. 95 (proof of 4.29); for
Chapter 19, only Definition 19.7 (p. 399); for Chapter 22, only pp. 468, 469,
473 and 480. None changes the conventions of pp. 4, 6 and 13 or the statements
of 3.23, 3.35, 4.3, 4.8, 4.9, 4.15, 4.17, 19.11, 19.17 or 22.39–22.42.
The errata snapshot of 2026-11-04 for the 2022 reprint (source ID
`milne-2022-algebraic-groups-errata-2026-11-04`, SHA-256
`78e5f297fb2c80c6dacf413fc5abd7f82ba3dd5e5f83b5a5205dfd93bf160d49`) has the
entry "p.478, proof of 22.42. The V_i in the first decomposition should be the
eigenspaces for the action of Z." It corrects the proof of (a) ⇒ (b), not the
statement. It is taken into account below.

## For the proof (in `SemisimpleRepresentationCharZeroProof`, not part of this module)

Milne's proof, printed pp. 477–478 (PDF pp. 493–494):

- (a) ⇒ (b). By Lemma 22.39 (printed p. 476, PDF p. 492; "A representation of
  G is semisimple if it becomes semisimple after an extension of scalars to
  k^a"), one may assume `k` algebraically closed; reductivity is kept by base
  change. Milne writes `G = Z·G′`, with `Z` the centre (of multiplicative type)
  and `G′` the derived group (semisimple). With the errata correction, `V` is
  the direct sum of the eigenspaces `V_i` of the diagonalizable group `Z`.
  Since `G′` commutes with `Z`, each `V_i` is `G′`-stable. By Proposition 22.41
  (printed p. 477: "Every finite-dimensional representation of G is
  semisimple" for semisimple `G`), each `V_i` is a direct sum of simple
  `G′`-modules `V_ij`. `Z` acts on `V_i` by scalars, so each `V_ij` is stable
  under `Z·G′ = G` and simple as a `G`-module.
- (b) ⇒ (c). Theorem 4.9, printed p. 87 (PDF p. 103): "The regular
  representation has a faithful finite-dimensional subrepresentation." The
  Library statement `AffineLinearEmbeddingStatement` is this existence
  assertion in the closed-immersion form.
- (c) ⇒ (a). Proposition 19.17, printed p. 401 (PDF p. 417): "If a connected
  group variety G admits a faithful semisimple representation, then its
  unipotent radical is trivial." `G` is a group variety by Cartier's theorem.
  Then Proposition 19.11(a), printed p. 400: "Let G be a connected group variety
  over a perfect field k. (a) If R_u(G) = e, then G is reductive." A field of
  characteristic zero is perfect.
