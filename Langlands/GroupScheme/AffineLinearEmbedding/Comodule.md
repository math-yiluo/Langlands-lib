# Matrix coefficients of finite subsets of a coalgebra over a field

Author: Worker 1240.

This helper module proves the linear-algebra core of the closed linear embedding
theorem `Langlands.GroupScheme.affineLinearEmbeddingStatement`
([`AffineLinearEmbeddingProof`](../AffineLinearEmbeddingProof.md)). It works with
any `K`-module `B` over a field `K` that carries Mathlib's `Coalgebra K B`
structure. Only the coalgebra axioms are used: coassociativity and the two counit
laws. No multiplication on `B` and no antipode appear in this module.

All declarations live in the namespace `Langlands.GroupScheme.AffineLinearEmbedding`.
Write `comul b = ∑ b₁ ⊗ b₂` for the comultiplication of `b : B` (Sweedler notation,
used only in this explanation).

## Translation operators

- `rightAct f : B →ₗ[K] B`, for a functional `f : Module.Dual K B`, is
  `TensorProduct.rid K B ∘ₗ f.lTensor B ∘ₗ comul`, that is `b ↦ ∑ f (b₂) • b₁`.
- `leftAct φ : B →ₗ[K] B` is `TensorProduct.lid K B ∘ₗ φ.rTensor B ∘ₗ comul`,
  that is `b ↦ ∑ φ (b₁) • b₂`.
- `rightAct_apply`, `leftAct_apply` unfold these definitions (`rfl`).

The following lemmas record the properties used later.

- `apply_leftAct g φ b : g (leftAct φ b) = φ (rightAct g b)`. Both sides equal
  `∑ φ (b₁) * g (b₂)`. The proof is induction on the tensor `comul b`.
- `rightAct_counit`, `leftAct_counit`: translation by the counit is the identity.
  These are the counit laws, applied through `simp` with Mathlib's simp lemmas
  `Coalgebra.lTensor_counit_comul` and `Coalgebra.rTensor_counit_comul`.
- `rightAct_rightAct g f a : rightAct g (rightAct f a) = rightAct (g ∘ₗ rightAct f) a`.
  Right translations compose. The proof rewrites both sides as maps applied to
  `(comul ⊗ id) (comul a)` and `(id ⊗ comul) (comul a)`. It then uses Mathlib's
  coassociativity `Coalgebra.coassoc_symm_apply` and an identity of linear maps
  on `B ⊗ B ⊗ B` checked on pure tensors (`TensorProduct.ext_threefold'`).
- `rightAct_leftAct g φ a : rightAct g (leftAct φ a) = leftAct φ (rightAct g a)`.
  Left and right translations commute. The proof follows the same pattern.
- `tensor_ext`: two tensors `t t' : B ⊗[K] B` are equal if
  `TensorProduct.rid K B (g.lTensor B t) = TensorProduct.rid K B (g.lTensor B t')` for
  every functional `g`. This lemma needs no coalgebra structure. It chooses a
  basis `b` of `B` (`Basis.ofVectorSpace`). The coordinate `i` of
  `TensorProduct.equivFinsuppOfBasisRight b u` equals the contraction of `u` with
  `b.coord i`, and that linear equivalence is injective.
- `exists_fg_rightAct a`: there is a finitely generated subspace `U` of `B`
  containing `rightAct f a` for every functional `f`. Write `comul a` as a finite
  sum of pure tensors (`TensorProduct.exists_finset`). Then `U` is the span of
  their first factors.

## Main result: `exists_matrix_coefficients`

For every finite set `S : Finset B` there are `N : ℕ` and a matrix
`M : Matrix (Fin N) (Fin N) B` such that

- `comul (M i j) = ∑ l, M i l ⊗ₜ[K] M l j` for all `i j`;
- `counit (M i j) = (1 : Matrix (Fin N) (Fin N) K) i j` for all `i j`;
- `(S : Set B) ⊆ Submodule.span K (Set.range fun p : Fin N × Fin N => M p.1 p.2)`.

### Proof

1. Let `W` be the span of all `rightAct f a` with `a ∈ S` and `f : Module.Dual K B`.
   By `exists_fg_rightAct`, `W` lies in the finite supremum `S.sup U` of finitely
   generated subspaces (`Submodule.fg_finset_sup`). Hence `W` is
   finite-dimensional. Taking `f = counit` shows `S ⊆ W` (`rightAct_counit`).
   `W` is stable under every `rightAct g`: by `rightAct_rightAct`, the generator
   `rightAct g (rightAct f a)` equals `rightAct (g ∘ₗ rightAct f) a`, again a
   generator.
2. Let `N = finrank K W` and `e : Basis (Fin N) K W` (`Module.finBasis`). The
   inclusion `W → B` has a linear left inverse `P : B →ₗ[K] W`
   (`LinearMap.exists_leftInverse_of_injective`). Put `φ i = e.coord i ∘ₗ P`.
   Then every `w ∈ W` satisfies `w = ∑ i, φ i w • e i`, and
   `φ i (e j) = (1 : Matrix _ _ K) i j`.
3. Define `M i j = leftAct (φ i) (e j)`. For every functional `g`, the lemma
   `apply_leftAct` and the expansion of step 2 applied to
   `rightAct g (e j) ∈ W` give `rightAct g (e j) = ∑ i, g (M i j) • e i`. Contracting
   with all `g` (`tensor_ext`) yields `comul (e j) = ∑ i, e i ⊗ₜ M i j`. So `W` is
   a subcomodule and `M` is its matrix of coefficients, as in Milne's notation
   `Δ(e_j) = ∑ᵢ eᵢ ⊗ a_{ij}`.
4. Comultiplication of `M`. By `tensor_ext` it suffices to compare contractions
   with any `g`. Using `rightAct_leftAct` and step 2,
   `rightAct g (M i j) = leftAct (φ i) (rightAct g (e j))
   = ∑ l, g (M l j) • leftAct (φ i) (e l) = ∑ l, g (M l j) • M i l`. This is the
   contraction of `∑ l, M i l ⊗ₜ M l j` with `g`.
5. Counit of `M`. By `apply_leftAct` with `g = counit`,
   `counit (M i j) = φ i (rightAct counit (e j)) = φ i (e j)`, which is the
   identity-matrix entry by step 2.
6. Span. By `leftAct_counit` and step 3,
   `e j = leftAct counit (e j) = ∑ i, counit (e i) • M i j`. So each basis vector
   lies in the span of the entries of `M`. Every `a ∈ S` lies in `W`, so it is a
   linear combination of the `e i`.

## Relation to the literature

J. S. Milne, *Algebraic Groups* (2017), Proposition 4.7 (printed p. 86) shows
that every element of a comodule lies in a finite-dimensional subcomodule. The
proof of Theorem 4.9 (printed p. 87) applies this to the regular comodule
`Δ : O(G) → O(G) ⊗ O(G)`. It takes a finite-dimensional subcomodule `V`
containing algebra generators, writes `Δ(e_j) = ∑ᵢ eᵢ ⊗ a_{ij}` and uses the
counit to get `e_j = ∑ᵢ ε(eᵢ) a_{ij}`.

This module proves the regular-comodule case needed there, with different
local arguments. Milne proves Proposition 4.7 with the structure constants of a
basis of `O(G)`. Here the subcomodule `W` is instead the span of all right
translates `rightAct f a`, and the comodule property is shown by contracting with
functionals. The matrix identities for `comul (M i j)` and `counit (M i j)` are the
standard identities for matrix coefficients of a comodule. Milne uses them
through the map `O(GL_V) → A` in (4.1). Here they are proved directly from
coassociativity and the counit laws. Step 6 is Milne's counit argument.
