# The local–global principle for embeddings of maximal subfields

Module: `Langlands.Algebra.CentralSimple.NumberFieldLocalGlobalEmbeddingStatement`.

`Langlands.CentralSimple.NumberFieldLocalGlobalEmbeddingStatement.{u}` is a proposition; this
module states it and does not prove it.

## The statement

It quantifies over a number field `F`, a finite extension field `E` of `F`
(`FiniteDimensional F E`), a finite-dimensional central simple `E`-algebra `B`
(`FiniteDimensional E B`, `Algebra.IsCentral E B`, `IsSimpleRing B`) that is an `F`-algebra
through `E` (`IsScalarTower F E B`), and a field `P` that is a finite-dimensional `E`-algebra
and an `F`-algebra through `E` (`IsScalarTower F E P`), all in one universe `u`.

The hypotheses are:

1. `Module.finrank E B = Module.finrank E P ^ 2`: the degree `[P : E]` is the degree `n` of
   `B`, the dimension of a maximal commutative subalgebra.
2. At every place `v` of `F` (`Global.Place F`, archimedean and finite), with
   `K_v = Global.placeCompletion F v` the actual completion, there is an injective
   `K_v`-algebra homomorphism `φ_v : K_v ⊗[F] P → K_v ⊗[F] B` with
   `φ_v (1 ⊗ e) = 1 ⊗ e` for every `e ∈ E` (the images of `E` in `P` and in `B`).

The conclusion is `Nonempty (P →ₐ[E] B)`: there is an `E`-algebra homomorphism `P → B`.
Since `P` is a field and `B` is nonzero, such a homomorphism is injective, so `P` is
isomorphic to a maximal subfield of `B`.

## Source

G. Prasad and A. S. Rapinchuk, *Local-global principles for embedding of fields with
involution into simple algebras with involution*, Comment. Math. Helv. 85 (2010), cited in its
arXiv version 0806.0596v5 (source `prasad-rapinchuk-2010-embedding-fields-involution`).

Proposition 2.7, p. 9: "Let `A` be a central simple algebra of dimension `n²` over a global
field `L`, and `E` be an `n`-dimensional commutative étale `L`-algebra. Then an `L`-embedding
`ε : E ↪ A` exists if and only if for every `w ∈ V^L` there exists an `L_w`-embedding
`ε_w : E ⊗_L L_w ↪ A ⊗_L L_w`." The source derives it from Proposition 2.6, p. 9 (an étale
algebra `∏ E_j` of dimension `n` embeds in `A` if and only if each field `E_j` splits `A`) and
the injectivity of `Br(F) → ⊕_w Br(F_w)` for a global field `F`.

The present statement is the case where the étale algebra is a field `P`, with the local
conditions indexed by the places of the subfield `F` instead of the places of the centre `E`.
The passage between the two is the first paragraph of the proof of Theorem 4.1, p. 13, of the
same paper: for a place `v` of `F`, `K_v ⊗[F] E` is the product of the completions `E_w` over
the places `w` of `E` above `v`, so that `K_v ⊗[F] P` and `K_v ⊗[F] B` are the products of the
`E_w ⊗[E] P` and the `E_w ⊗[E] B`. A homomorphism `φ_v` as in hypothesis 2 is
`K_v ⊗[F] E`-linear, because it is `K_v`-linear and the identity on `E`, so it is the product of
injective `E_w`-algebra homomorphisms `E_w ⊗[E] P → E_w ⊗[E] B`; these are the local embeddings
of Proposition 2.7 at every place `w` of `E`.
