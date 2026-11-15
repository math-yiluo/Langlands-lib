# Normal unipotent subgroups and semisimple representations

`Langlands.GroupScheme.SemisimpleRepresentationUnipotentStatement.{u}` is a
Prop-valued definition. This module defines the proposition and proves
nothing.

## Statement

The proposition says: for every field `k : Type u` and every group scheme
`G : GroupScheme (Spec (CommRingCat.of k))` whose structure morphism is
locally of finite type and affine, the following two assertions hold.

(19.16) For every group scheme `H` over `k` and every homomorphism
`i : H ⟶ G` with `IsClosedSubgroup i`, `IsUnipotent H` and
`(SubgroupFunctor.range i).IsNormal`, and for every `n : ℕ` and every
`ρ : MatrixRepresentation G (Fin n)` with `IsSemisimpleRep n ρ`,

```text
ρ.restrict i = MatrixRepresentation.trivial H (Fin n)
```

(19.17) If `Smooth G.X.hom` and `ConnectedSpace G.X.left`, and if some
`ρ : MatrixRepresentation G (Fin n)` satisfies `IsClosedSubgroup ρ` and
`IsSemisimpleRep n ρ`, then `HasTrivialUnipotentRadical G`.

Here `IsSemisimpleRep` is a local abbreviation inside the statement:

```text
IsSemisimpleRep n ρ :=
  sSup {W : Submodule k (Fin n → k) | ρ.IsStableSubspace W ∧ W ≠ ⊥ ∧
    ∀ U : Submodule k (Fin n → k), ρ.IsStableSubspace U → U ≤ W →
      U = ⊥ ∨ U = W} = ⊤
```

In words: let `G` be an affine algebraic group over a field `k`.

- A normal unipotent algebraic subgroup of `G` acts trivially on every
  semisimple finite-dimensional representation of `G`.
- If `G` is a connected group variety (smooth and connected) with a faithful
  semisimple finite-dimensional representation, then the unipotent radical of
  `G` is trivial.

Every ingredient is an existing declaration, used without change:

- `MatrixRepresentation G (Fin n)` (from
  [`MatrixRepresentation`](../MatrixRepresentation.md)) is a homomorphism of
  group schemes `ρ : G ⟶ GL_n` over `k`, that is, a representation of `G` on
  `kⁿ` with its standard basis. Every finite-dimensional representation is
  isomorphic to one of these. `ρ.restrict i` is the composite `i ≫ ρ`, the
  restriction of `ρ` to `H`. `MatrixRepresentation.trivial H (Fin n)` is the
  homomorphism `H ⟶ GL_n` that sends every point to the identity matrix. So
  the equation of (19.16) says that `H` acts trivially on `kⁿ`.
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
- `IsClosedSubgroup i` (from [`Reductive.Basic`](Basic.md)) says that the
  morphism of schemes underlying `i` is a closed immersion. For `ρ` this is
  how the Library's `AffineLinearEmbeddingStatement` expresses a faithful
  representation.
- `IsUnipotent H` (from [`Reductive.Basic`](Basic.md)) says that for every
  nonempty finite index type `m` and every `σ : MatrixRepresentation H m`
  there is a nonzero vector of `kᵐ` fixed by `σ` (over every test scheme).
- `SubgroupFunctor.range i` is the subgroup functor of `G` whose points over a
  test scheme are the points of `G` that factor through `i`, and `IsNormal`
  says that these subgroups are normal in the groups of points of `G` over
  every test scheme.
- `HasTrivialUnipotentRadical G` (from [`Reductive.Basic`](Basic.md)) says:
  for every closed subgroup `j : H ⟶ G` with `H` smooth, connected and
  unipotent and with normal range, `SubgroupFunctor.range j = ⊥`. This is
  over `k` itself, not over an algebraic closure.

Both parts keep the hypotheses `[LocallyOfFiniteType G.X.hom]` and
`[IsAffineHom G.X.hom]`, so `G` is an affine algebraic group, as in Milne's
chapter 19 (see the provenance). `H` need not be assumed affine or of finite
type: a closed subgroup of `G` is both.

## Provenance (derived)

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups` (SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`). Printed page
numbers are given; the PDF page is the printed page plus 16.

The two parts are, on printed p. 401 (PDF p. 417):

- Lemma 19.16: "A normal unipotent algebraic subgroup U of an algebraic group
  G acts trivially on every semisimple representation of G."
- Proposition 19.17: "If a connected group variety G admits a faithful
  semisimple representation, then its unipotent radical is trivial."

The surrounding conventions are:

- Algebraic groups. "An algebraic group over k is a group object in the
  category of algebraic schemes over k", and "an algebraic k-scheme is a
  scheme of finite type over k" (printed p. 6, PDF p. 22). The notation
  section, printed p. 4 (PDF p. 20), says "After p. 162, all algebraic groups
  are affine." Printed p. 162 (PDF p. 178): "We now concentrate on affine
  algebraic groups. By "algebraic group" we shall mean "affine algebraic
  group" and by "group variety" we shall mean "affine group variety"." The
  Lean statement therefore assumes that `G` is affine and locally of finite
  type (hence of finite type, as an affine morphism is quasi-compact).
- Group varieties. Printed p. 13 (PDF p. 29): ""group variety" = "smooth
  algebraic group"". A connected group variety is therefore an affine
  algebraic group that is smooth and connected; this is `Smooth G.X.hom` and
  `ConnectedSpace G.X.left` together with the standing hypotheses.
- Algebraic subgroups. Definition 1.3 (printed p. 7, PDF p. 23) defines an
  algebraic subgroup of `G` as an algebraic group `H` over `k` "such that H is
  a k-subscheme of G and the inclusion map is a homomorphism of algebraic
  groups", and Proposition 1.41 (printed p. 18, PDF p. 34) says "Algebraic
  subgroups of algebraic groups are closed (in the Zariski topology)." So an
  algebraic subgroup is a closed subgroup `i : H ⟶ G` in the sense of
  `IsClosedSubgroup`. Definition 1.51(a) (printed p. 21, PDF p. 37): "An
  algebraic subgroup H of G is normal if H(R) is normal in G(R) for all small
  k-algebras R." This is `(SubgroupFunctor.range i).IsNormal`, which tests
  all schemes over `k`, including all affine ones.
- Unipotent groups. 6.45 (printed p. 135, PDF p. 151): "An algebraic group G
  is said to be unipotent if every nonzero representation of G has a nonzero
  fixed vector." Its footnote 2 gives the finite-dimensional form:
  "Equivalently, for every finite-dimensional representation r: G → GL_V of G,
  there is a basis such that r(G) ⊂ U_n." `IsUnipotent` asks for fixed
  vectors in finite-dimensional representations only. This is equivalent:
  every nonzero representation contains a nonzero finite-dimensional
  subrepresentation (Corollary 4.8 below), and a fixed vector in it is a
  fixed vector of the whole representation.
- Unipotent radical. 6.46 (printed p. 135): "Let G be a connected group variety
  over k. It follows from 6.45 that among the connected normal unipotent
  subgroup varieties of G, there is a largest one. This is called the
  unipotent radical R_u(G) of G." A subgroup variety is an algebraic subgroup
  whose underlying scheme is a variety (Definition 1.3), that is, a smooth
  algebraic subgroup (p. 13, above). Corollary 14.8 (printed p. 282, PDF p. 298):
  "Every algebraic group contains a largest smooth connected normal unipotent
  subgroup." So `R_u(G) = e` if and only if every smooth connected normal
  unipotent algebraic subgroup of `G` is trivial, which is
  `HasTrivialUnipotentRadical G`. As in Milne, this is the unipotent radical
  over `k`, not the geometric one.
- Representations. Chapter 4 opens, printed p. 83 (PDF p. 99), with
  "Throughout this chapter, G is an affine algebraic group over a field k." On
  the same page: "A linear representation r is faithful if r(R): G(R) →
  Aut_{R-linear}(V_R) is injective for all k-algebras R. For finite-dimensional
  linear representations, this is equivalent to r being a closed immersion
  (3.35). A representation is trivial if r(G) = e." "Acts trivially" in 19.16
  is this triviality of the restriction to `U`.
- Subrepresentations. The proof of Corollary 4.8, printed p. 86 (PDF p. 102),
  states: "A subspace W of V is stable under G if and only if it is an
  O(G)-subcomodule of V". These subspaces are the subrepresentations.
  Corollary 4.8 itself: "Every representation of G is a filtered union of its
  finite-dimensional subrepresentations."
- Semisimple. Definition 4.15, printed p. 90 (PDF p. 106): "A representation
  of an algebraic group is simple if it is ≠ 0 and its only subrepresentations
  are 0 and itself. It is semisimple if it is a sum of simple
  subrepresentations." `IsSemisimpleRep` is this definition for the
  representation `ρ` on `kⁿ`. Proposition 4.16 (same page): "Every simple
  representation of an algebraic group is finite-dimensional."

The provenance is derived for these reasons:

- Milne states a lemma and a proposition separately. The Lean statement is
  their conjunction, in the same order.
- Milne's representations need not be finite-dimensional. The Lean statement
  covers finite-dimensional representations, given in coordinates as
  homomorphisms to `GL_n` on `kⁿ`. Nothing of the mathematical content is
  lost, for these reasons (not formalized):
  - (19.16) A semisimple representation `V` is a sum of simple
    subrepresentations, each finite-dimensional (4.16) and semisimple. If `U`
    acts trivially on each of them, it acts trivially on their sum `V`.
  - (19.17) Let `V = Σ_{i ∈ I} S_i` be a faithful semisimple representation
    with simple `S_i`. For a finite subset `J` of `I`, the kernel `K_J` of the
    action of `G` on `S_J = Σ_{j ∈ J} S_j` is an algebraic subgroup, and
    `K_J ⊇ K_{J'}` when `J ⊆ J'`. A point of `G` acts trivially on `V_R` if
    and only if it acts trivially on every `(S_i)_R`, so the intersection of
    all `K_J` is the kernel of `V`, which is `e`. The ideals of the `K_J` in
    the noetherian ring `O(G)` form an upward directed family, so one of them
    is the largest and equals their sum, the ideal of the intersection. Hence
    `K_J = e` for some finite `J`, and `S_J` is a faithful semisimple
    finite-dimensional representation.
- Faithfulness of a finite-dimensional representation is expressed by the
  closed immersion condition, which Milne states is equivalent (3.35).
- `k`, `G` and `H` lie in an arbitrary universe `u`, and the test algebras in
  `IsStableSubspace` lie in the same universe. This is a formalization
  convention. The universal point of `G`, with values in its coordinate ring,
  is one of these tests, so stability is the subcomodule condition.

Errata. The official errata snapshot of 2026-11-02 for the 2017 book (source
ID `milne-2017-algebraic-groups-errata-2026-11-02`, SHA-256
`a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`) lists, for
Chapter 1, a note that Notation 3.2 should be placed earlier and corrections
on p. 18 (the proof of 1.40), p. 20 (1.45), p. 21 (Definition 1.48) and p. 26
(the proof of 1.65); under the heading Chapter 3, corrections on p. 80 (3.52)
and p. 85 ("G_W is the stabilizer of W in G (not V)"); for Chapter 4, only a
correction on p. 95 (proof of 4.29); for Chapter 5, only p. 123 (Exercise
5-7); for Chapter 6, only p. 129 (6.19) and p. 136 (Example 6.48); under the
heading Chapter 14, only p. 273 (Theorem 13.47(c)); for Chapter 19, only
Definition 19.7 (p. 399). None changes the conventions of pp. 4, 6, 13 and 162
or Definitions 1.3, 1.51 and 4.15, 1.41, 4.8, 4.16, 5.15, 6.45, 6.46, 14.8,
19.16 or 19.17.

## For the later proof (not part of this unit)

Milne's proofs, printed p. 401:

- 19.16: "Let V be a semisimple representation of G, and let W be a simple
  subrepresentation of V. Because U is normal, W^U is stable under G (see
  5.15), and because U is unipotent, W^U ≠ 0. Therefore W^U = W. As V is a sum
  of its simple subrepresentations, it follows that U acts trivially on V."
  Lemma 5.15 (printed p. 102, PDF p. 118): "Let N be an algebraic subgroup of
  an algebraic group G, and let (V, r) be a representation of G. If N is
  normal in G, then V^N is stable under G." Applied to the representation on
  `W`, this gives that `W^U` is a subrepresentation of `W`; it is nonzero
  because `U` is unipotent and `W ≠ 0`, so it equals `W` by simplicity.
- 19.17: "Let (V, r) be a faithful semisimple representation of G. According
  to the lemma, r(R_u(G)) = e, and so R_u(G) = e." In the Lean form: for a
  closed subgroup `j : H ⟶ G` as in `HasTrivialUnipotentRadical`, part (19.16)
  gives `j ≫ ρ = trivial`. A closed immersion is a monomorphism, so every
  point of `H` maps to the identity point of `G`, that is,
  `SubgroupFunctor.range j = ⊥`. Smoothness and connectedness of `G` are not
  used in this argument; they are part of Milne's statement because `R_u(G)`
  is defined (6.46) for connected group varieties.

Library material that may help: `MatrixRepresentation.normalFixedSubrepresentation`
(in [`MatrixRepresentation.NormalFixedRepresentation`](../MatrixRepresentation/NormalFixedRepresentation.md))
realizes the fixed space of a normal affine subgroup as a representation of
`G`; `IsStableSubspace.isStableCoordinates` and `restrictCoordinates` give a
stable subspace in coordinates; `mulVec_mem_fixedSubmodule` (in
[`Reductive.GeneralLinear`](GeneralLinear.md)) shows that the matrices in
`GL_n(k)` map the fixed vectors of a normal subgroup of `GL_n` to fixed
vectors, a special case of Lemma 5.15 used there for `GL_n` along the route
of Lemma 19.16.
