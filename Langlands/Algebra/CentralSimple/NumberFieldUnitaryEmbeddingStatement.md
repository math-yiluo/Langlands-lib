# Embeddings of fields with involution into algebras with unitary involution

Module: `Langlands.Algebra.CentralSimple.NumberFieldUnitaryEmbeddingStatement`.

`Langlands.CentralSimple.NumberFieldUnitaryEmbeddingStatement.{u}` is a proposition; this
module states it and does not prove it.

## The statement

It quantifies over a number field `F`, a separable quadratic extension `E/F`
(`Algebra.IsQuadraticExtension F E`, `Algebra.IsSeparable F E`), a finite-dimensional central
simple `E`-algebra `B` that is an `F`-algebra through `E`, and a field `P` that is a
finite-dimensional `E`-algebra and an `F`-algebra through `E`, all in one universe `u`. It
takes `F`-linear involutions `τ : FirstKindInvolution F B` and
`σ : FirstKindInvolution F P` (on the commutative ring `P`, an involution is an `F`-algebra
automorphism of order at most two) that both act on `E` by
`SU3Root.conjugation F E`, the nontrivial automorphism of `E/F`. So `τ` is an involution of
the second kind, and `σ` is nontrivial.

The hypotheses are:

1. `Module.finrank E B = Module.finrank E P ^ 2`: the degree `[P : E]` is the degree `n` of
   `B`, so that `P` has the dimension of a maximal commutative subalgebra of `B`.
2. At every place `v` of `F`, with `K_v = Global.placeCompletion F v` (archimedean and finite
   completions), there is a `K_v`-algebra homomorphism
   `φ_v : K_v ⊗[F] P → K_v ⊗[F] B` that is injective, satisfies
   `φ_v (1 ⊗ e) = 1 ⊗ e` for `e ∈ E` (the images of `E` in `P` and `B`), and intertwines the
   involutions: `φ_v (σ_{K_v} y) = τ_{K_v} (φ_v y)`, where `σ_{K_v} = σ.baseChange K_v` and
   `τ_{K_v} = τ.baseChange K_v` are `id ⊗ σ` and `id ⊗ τ`.

The conclusion is an `E`-algebra homomorphism `φ : P →ₐ[E] B` with `φ (σ p) = τ (φ p)` for
all `p ∈ P`. Since `P` is a field and `B` is nonzero, `φ` is injective, so `φ` is an
embedding of `E`-algebras with involution `(P, σ) → (B, τ)`.

The local homomorphisms are `E ⊗[F] K_v`-linear because they are `K_v`-linear and the
identity on `E`; at a place where `E ⊗[F] K_v` is a field this is an embedding of
`E ⊗[F] K_v`-algebras, and at a split place it is a pair of embeddings on the two factors.

## Source

G. Prasad and A. S. Rapinchuk, *Local-global principles for embedding of fields with
involution into simple algebras with involution*, Comment. Math. Helv. 85 (2010), cited in its
arXiv version 0806.0596v5 (source `prasad-rapinchuk-2010-embedding-fields-involution`),
Theorem 4.1, p. 13: "Let `A` be a central simple algebra over a global field `L`, of
dimension `n²`, with an involution `τ` of the second kind, `K = L^τ`, and let `E/L` be a
field extension of degree `n` provided with an involutive automorphism `σ` such that
`τ|L = σ|L`. Suppose that for each `v ∈ V^K` there exists an `(L ⊗_K K_v)`-embedding
`ι_v : (E ⊗_K K_v, σ ⊗ id_{K_v}) ↪ (A ⊗_K K_v, τ ⊗ id_{K_v})` of algebras with
involutions. Then there exists an `L`-embedding `ι : (E, σ) ↪ (A, τ)` of algebras with
involutions." The same result is assertion (i) of Theorem A, p. 2. The source's `K`, `L`, `A`
and `E` are `F`, `E`, `B` and `P` here; the Lean statement is the case of a number field `K`.
Example 4.6 of the same paper shows that the conclusion can fail when the field `P` is
replaced by a commutative étale algebra.

The embedding problem is the one solved within the proof of the unitary norm theorem in
Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994), §6.7, proof of
Theorem 6.28, printed pp. 366–368 (PDF pp. 376–378), source
`platonov-rapinchuk-1994-algebraic-groups-number-theory`.

## Remark on proofs

The proof of Lemma 4.3 in Prasad–Rapinchuk (pp. 16–17) uses the Hasse principle for
`SU(A, τ)`, which Platonov–Rapinchuk (§6.7, pp. 359–360) deduce from Landherr's theorem and
the unitary norm theorem; the module
`Langlands.Algebra.CentralSimple.NumberFieldUnitaryNormReduction` derives the unitary norm
theorem (`NumberFieldUnitaryNormStatement`) from the present statement. The following
argument avoids that Hasse principle. Fix an embedding `ε : P → B` (it exists by the
Brauer–Hasse–Noether theorem, since the local embeddings make every completion of `P` split
`B`). By Skolem–Noether and Hilbert's Theorem 90 for `P/P^σ` there is a unit `t` of `B` with
`τ(t) = t` and `τ(ε(p)) = t ε(σ p) t⁻¹` for `p ∈ P`. For a unit `s`, the embedding
`p ↦ s⁻¹ ε(p) s` intertwines `σ` and `τ` exactly when `s τ(s) = ε(b) t⁻¹` with
`b ∈ (P^σ)ˣ`. The solvability of `s τ(s) = ε(b) t⁻¹` over `K_v` depends only on the class
of `b` modulo the norms of `(P ⊗[F] K_v)ˣ` (replace `s` by `ε(p) s`, which multiplies `b` by
`p σ(p)`). Let `S` be the finite set of places of `F` that are archimedean, ramified in `E`,
or at which `Nrd(t)` is not a unit. At `v ∉ S` take `b_v = 1`: at a split place every
`τ`-symmetric unit has the form `s τ(s)`, and at a finite place where `E/F` is unramified and
`Nrd(t)` is a unit, `Nrd(t⁻¹)` is a local norm from `E`, so `t⁻¹` has the form `s τ(s)` by the
local criterion in Platonov–Rapinchuk, printed p. 363 (PDF p. 373). At `v ∈ S` the local
embeddings give local solutions `b_v` (two embeddings of `P ⊗[F] K_v` as maximal commutative
subalgebras of `K_v ⊗[F] B` are conjugate). Taking reduced norms in
`s_v τ(s_v) = ε(b_v) t⁻¹` shows that `N_{P^σ ⊗ K_v / K_v}(b_v) Nrd(t)⁻¹` is a local norm from
`E`. By functoriality of local reciprocity, the product over the places `w` of `P^σ` above `v`
of the norm-residue symbols of `P/P^σ` at the components of `b_v` is the norm-residue symbol of
`E/F` at `N_{P^σ ⊗ K_v / K_v}(b_v)`, hence at `Nrd(t)`. This finitely supported family of local
classes therefore has trivial total product by global reciprocity for `E/F` at `Nrd(t) ∈ Fˣ`,
and global class field theory for the quadratic extension `P/P^σ` gives a global `b` in all
these classes. Landherr's theorem (`NumberFieldLandherrStatement`) then solves
`s τ(s) = ε(b) t⁻¹` in `Bˣ`.
