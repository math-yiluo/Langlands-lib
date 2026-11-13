# Linear algebra for the split rank of `SL_m(D)`

Author: Worker 161.

This helper module proves three elementary facts. It is used only by the upper bound
`Langlands.GroupScheme.MatrixNormOneSplitRank.splitRank_le` in
`Langlands.GroupScheme.SimplyConnected.MatrixNormOneSplitRankUpper`. All declarations
are in the namespace `Langlands.GroupScheme.MatrixNormOneSplitRank`. The module adds
no hypotheses, axioms or proof holes and imports only Mathlib.

## Provenance

These are internal lemmas written for this proof, not translations of a cited
source. The facts themselves are standard: Peirce decomposition by a complete family
of orthogonal idempotents, the dimension of a nonzero right ideal of a matrix algebra
over a division ring, and a rank count in linear algebra over `ℚ`.

## Complete orthogonal idempotents

Let `A` be a finite-dimensional algebra over a field `K`. Let `e : ι → A` be a finite
family with `e i * e j = if i = j then e i else 0` (`hmul`) and `∑ i, e i = 1`
(`hsum`).

- `piece K e i` is the `K`-subspace `e i · A`, defined as the range of left
  multiplication by `e i`. `mem_piece_iff` unfolds membership.
- `mul_of_mem_piece`: for `x ∈ e j · A`, `e i * x` is `x` if `j = i` and `0` otherwise.
  It writes `x = e j * y` and uses `hmul`.
- `isInternal_piece`: `A` is the internal direct sum of the subspaces `e i · A`.
  Independence holds because left multiplication by `e i` kills every `e j · A` with
  `j ≠ i` and fixes `e i · A`. The subspaces span because `x = ∑ i, e i * x`.
- `pieceBasis K hmul hsum` is the basis of `A` collected from `Module.finBasis` of each
  piece, indexed by `Σ i, Fin (finrank K (e i · A))`. `pieceBasis_mem` places each
  vector in its piece, and `mul_pieceBasis` says `e i` acts on a basis vector of piece
  `a.1` as the Kronecker delta in `a.1` and `i`.
- `sum_finrank_piece`: `∑ i, finrank K (e i · A) = finrank K A`, by counting the
  adapted basis.
- `norm_sum_tmul`: for every commutative `K`-algebra `R` and `c : ι → R`,
  `Algebra.norm R (∑ i, c i ⊗ₜ e i) = ∏ i, c i ^ finrank K (e i · A)`. Here
  `Algebra.norm R` is the norm of the `R`-algebra `R ⊗[K] A`. The proof computes the
  matrix of left multiplication in the base-changed adapted basis
  (`Algebra.norm_eq_matrix_det`). On `1 ⊗ B a'` the element acts as `c a'.1`, so the
  matrix is `Matrix.diagonal fun a => c a.1`. Its determinant is a product over the
  sigma type, which `Fintype.prod_sigma` regroups.

## Right ideals of matrix algebras over division rings

Let `D` be a division ring that is a finite-dimensional `K`-algebra, and `n : ℕ`.

- `rowInsert q : (Fin n → D) →ₗ[K] Matrix (Fin n) (Fin n) D` places a vector in row `q`
  of an otherwise zero matrix.
- `le_finrank_range_mulLeft`: for every nonzero `e : Matrix (Fin n) (Fin n) D`,
  `n * finrank K D ≤ finrank K (e · M_n(D))`. Choose an entry `e p q ≠ 0`. The map
  `c ↦ e * rowInsert q c` lands in `e · M_n(D)`. It is injective: entry `(p, s)` of
  the product is `e p q * c s`, and `D` has no zero divisors. Its source has dimension
  `n * finrank K D`.

## Generating sets of `ℤ^I` with a positive relation

Let `I` be a finite type.

- `ratVec m` is the rational vector `fun i => (m i : ℚ)` of `m : I → ℤ`.
- `card_add_one_le_of_relation`: let `S` be a finite set of vectors in `I → ℤ` whose
  additive closure is all of `I → ℤ`. Let `r : (I → ℤ) → ℕ` be positive on `S`, with
  `∑ m ∈ S, r m • m = 0`. Then `Fintype.card I ≤ S.card - 1`. The proof uses the
  `ℚ`-linear map `φ : (S → ℚ) → (I → ℚ)`, `c ↦ ∑ s, c s • ratVec s`. Its range
  contains every `ratVec z`, by induction on the closure, and hence all of `I → ℚ`.
  If `S` is empty, then `I → ℤ` is trivial, so `I` is empty. Otherwise the coefficients
  `r` give a nonzero kernel vector. Rank–nullity then gives
  `card I + 1 ≤ card S`.
