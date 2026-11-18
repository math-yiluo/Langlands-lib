# Torus-weight grading of the pair Lie algebra

Module: `Langlands.GroupScheme.Rational.FreudenthalLieInterface`.

## Purpose

The Casimir proof of Freudenthal's multiplicity formula (Humphreys, *Introduction to Lie
Algebras and Representation Theory*, §22.3) works inside a Lie algebra of endomorphisms that
is graded by torus weights, has a one-dimensional piece for each root, and has a
degree-zero piece given by the torus. This module states those facts as a single
proposition about the tangent Lie algebra of a pair of representations. The proposition is
used as a hypothesis by the Casimir argument; it is proved separately from the structure of
split reductive groups.

## Setting

Let `p : SplitPinning G` be a split pinning over a field `k`, with split maximal torus `T`,
character lattice `X` and cocharacter lattice `Y`, and let `⟨μ, y⟩ ∈ ℤ` be the pairing
`p.rootDatum.toLinearMap μ y`. (By `IsRootDatumOf`, this is the canonical pairing of
characters and cocharacters of `T`.) Let `σ : MatrixRepresentation G m` and
`ρ : MatrixRepresentation G n` be finite matrix representations, and let
`U = (m → k) × (n → k)`, on which the Library's pair Lie algebra
`MatrixRepresentation.pairLieAlgebra σ ρ` acts by block-diagonal endomorphisms.

## Definitions

* `pairWeightSpace p σ ρ μ` is `U_μ = σ_μ × ρ_μ`, the product of the weight-`μ` spaces
  `p.representationWeightSpace σ μ` and `p.representationWeightSpace ρ μ`.
* `weightShift p σ ρ χ` is the subspace of `End_k(U)` of endomorphisms `f` with
  `f(U_μ) ⊆ U_{μ+χ}` for every `μ ∈ X`.
* `IsCocharacterAction p σ ρ y x` says that `x` acts on every `U_μ` by multiplication by the
  integer `⟨μ, y⟩`, viewed in `k`. This is how the differential of the cocharacter `y`
  acts on `U`.
* `pairLieGraded p σ ρ χ` is `g_χ = g ∩ weightShift p σ ρ χ`, where `g` is the underlying
  subspace of `pairLieAlgebra σ ρ`.

## The proposition `PairLieWeightData p σ ρ`

It is the conjunction of six statements:

1. **Grading:** `g` lies in the sum of the subspaces `g_χ` for `χ ∈ X`.
2. **Cocharacter elements:** for every `y ∈ Y` there is `x ∈ g` with
   `IsCocharacterAction p σ ρ y x`.
3. **Degree zero:** `g_0` lies in the `k`-span of all endomorphisms `x` with
   `IsCocharacterAction p σ ρ y x` for some `y ∈ Y`.
4. **Non-roots:** if `χ ≠ 0` is not a root of `p.rootDatum`, then `g_χ = 0`.
5. **Root lines:** for every root index `i`, `g_{α_i}` has dimension one over `k`, where
   `α_i = p.rootDatum.root i`.
6. **Faithfulness on cocharacters:** for every nonzero `y ∈ Y` there is a weight `μ` of `σ`
   (that is, `p.representationWeightSpace σ μ ≠ ⊥`) with `⟨μ, y⟩ ≠ 0`.

## The statement `PairLieWeightDataStatement`

`PairLieWeightDataStatement.{u}` says: for every field `k : Type u` of characteristic zero,
every affine, locally finite type group scheme `G` over `k` with a split pinning `p`, every
`σ : MatrixRepresentation G (Fin N)` whose underlying morphism is a closed immersion
(`IsClosedSubgroup σ`), and every `ρ : MatrixRepresentation G (Fin n)`, the proposition
`PairLieWeightData p σ ρ` holds.

## Mathematical content

When `σ` is a closed embedding, the tangent map of `σ` is injective, so `g` is isomorphic to
the Lie algebra of `G`. Under this isomorphism, `g_χ` corresponds to the `χ`-weight space
of the adjoint action of the split maximal torus `T`. Statement 1 is the weight
decomposition of the adjoint representation of `T`. Statements 2 and 3 say that the
degree-zero part is the Lie algebra of the centralizer of `T`, which is `Lie(T) = Y ⊗ k`
because a maximal torus of a connected reductive group is its own centralizer. Statements
4 and 5 say that the nonzero weights of `T` on `Lie(G)` are exactly the roots, each with a
one-dimensional weight space. Statement 6 holds because `T` acts faithfully through `σ`.
These are standard facts about split reductive groups; see Jantzen, *Representations of
Algebraic Groups*, II.1.1–II.1.2, or Milne, *Algebraic Groups*, Chapter 21.

This module only states these facts; it proves nothing beyond the membership lemma
`mem_weightShift`, which unfolds the definition of `weightShift`.
