# Simultaneous triangularization of connected solvable matrix groups

Worker 277.

This module turns the common-eigenvector theorem of
`Langlands.Group.LieKolchin.CommonEigenvector` into simultaneous triangularization of a
matrix representation. The hypotheses on the group `G` and the field `k` are the same:
`k` is algebraically closed, `G` is solvable and preconnected, and `hmul`, `hinv` and
`hcomm` hold. The representation `ρ : G →* Matrix (Fin n) (Fin n) k` must satisfy the
closedness hypothesis: `{g | Λ (ρ g) = c}` is closed for every linear functional `Λ` on
matrices and every `c : k`.

## Declarations

- `mul_stepP_apply_zero`, `ext1_mul_mul_succ_zero` and `ext1_mul_mul_succ_succ` are
  block computations. They use the published elementary matrices of
  `Langlands.Algebra.GradedHopf.Triangular`. For a vector `v` with `v i₀ ≠ 0`,
  `stepP v i₀` is an invertible matrix with first column `v`, and `stepQ v i₀` is its
  inverse (`stepQ_mul_stepP`). `ext1 M` is the block matrix `diag(1, M)`. The lemmas say:
  the first column of `M * stepP v i₀` is `M *ᵥ v`; conjugating by `ext1` preserves a
  zero first column below the corner; and on the lower-right block it is ordinary
  conjugation of the `Fin.succ` submatrix.
- `exists_mulVec_eigenvector`: a common eigenvector `v ≠ 0` with `ρ g *ᵥ v = c • v` for all
  `g`, for `n + 1 ≥ 1`. The proof transports `ρ` along
  `Matrix.toLinAlgEquiv'` and applies `exists_common_eigenvector_of_isSolvable`. The
  closedness hypothesis is transported by composing functionals with this linear
  equivalence.
- `exists_triangularizing hmul hinv hcomm n ρ hR`: there are matrices `P` and `Q` with
  `P * Q = 1` such that `(Q * ρ g * P) i j = 0` whenever `j < i`, for every `g`. So every
  `Q * ρ g * P` is upper triangular.

## Proof of `exists_triangularizing`

Induction on `n`. For `n = 0` take `P = Q = 1`; there are no indices. For `n + 1`:

1. Choose a common eigenvector `v` and an index `i₀` with `v i₀ ≠ 0`. Put
   `P₁ = stepP v i₀` and `Q₁ = stepQ v i₀`, so `Q₁ * P₁ = P₁ * Q₁ = 1`.
2. Let `B g = Q₁ * ρ g * P₁`. Its first column is `Q₁ *ᵥ (ρ g *ᵥ v) = c • Q₁ *ᵥ v`. This is
   `c` times the first standard basis vector, so the entries below the corner vanish.
   `B` is multiplicative because `P₁ * Q₁ = 1`.
3. The lower-right blocks `ρ₂ g = (B g).submatrix Fin.succ Fin.succ` form a monoid
   homomorphism `G →* Matrix (Fin n) (Fin n) k`, because the first column of each `B g`
   vanishes below the corner. Each linear condition on `ρ₂` is a linear condition on
   `ρ` composed with the linear map `M ↦ (Q₁ * M * P₁).submatrix Fin.succ Fin.succ`.
   So `ρ₂` satisfies the closedness hypothesis.
4. The induction hypothesis gives `P₂` and `Q₂` triangularizing `ρ₂`. Then
   `P = P₁ * ext1 P₂` and `Q = ext1 Q₂ * Q₁` satisfy `P * Q = 1`, and
   `Q * ρ g * P = ext1 Q₂ * B g * ext1 P₂`. Below the diagonal, the entries in the first
   column vanish by step 2. The other entries are those of `Q₂ * ρ₂ g * P₂`, which vanish
   by the induction hypothesis.

## Provenance

This is the matrix form of J. S. Milne, *Algebraic Groups* (2017), Theorem 16.30
and Corollary 16.32, printed pp. 334–335 (`milne-2017-algebraic-groups`): over an
algebraically closed field, a connected solvable group acting on a finite-dimensional
space stabilizes a full flag. The source deduces trigonalizability from the existence of
one-dimensional quotients of simple representations. This module builds the flag
explicitly instead, by the induction above, with the abstract topological hypotheses
in place of the algebraic-group structure.
