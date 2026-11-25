# Bounds for the toral Iwasawa coordinate of `GL_n(ℝ)`

Helper module for the convergence of the real unequal-rank Rankin–Selberg integrals (towards
`Langlands.Global.RankinSelbergGlobal.RealPlaceFunctionalEquationStatement`). Every declaration is proved, with no axioms beyond Lean's standard ones
(`propext`, `Classical.choice`, `Quot.sound`).

All declarations are in the namespace `Langlands.Global.RankinSelbergGlobal.RealIwasawa`, which
extends the module `RealIwasawa`. There every `g ∈ GL_n(ℝ)` is written
`g = npart g · torus(alpha g) · kpart g`, with `npart g` upper unipotent,
`torus z = diag(exp z_i)` and `kpart g` orthogonal. Equivalently `g = bpart g · kpart g` with
`bpart g` upper triangular with diagonal entries `exp(alpha_i g)`. This module bounds the toral
coordinate `α(g) = alpha g` by the entries of `g` and of `g⁻¹`.

## Orthogonal matrices and the triangular coordinate

- `unitary_mul_transpose`: `k ᵗk = 1` for `k` in `unitaryCompact ℝ n`.
- `bpart_inv_diag`: the diagonal entries of `(bpart g)⁻¹` are `exp(−α_i(g))`. Both matrices are
  upper triangular, so the diagonal of their product `1` is the product of the diagonals.
- `inv_val_eq`: `g⁻¹ = ᵗ(kpart g) · (bpart g)⁻¹`.

## Row and column bounds

- `exp_two_mul_alpha_le` (**row bound**): `exp(2 α_i(g)) ≤ ∑_q g_(iq)²`. Proof: with
  `B = bpart g` and `k = kpart g`, `∑_q g_(iq)² = (g ᵗg)_(ii) = (B ᵗB)_(ii) = ∑_p B_(ip)²`, which
  is at least `B_(ii)² = exp(2 α_i(g))`.
- `exp_neg_two_mul_alpha_le` (**column bound**): `exp(−2 α_i(g)) ≤ ∑_p ((g⁻¹)_(pi))²`. Proof: with
  `C = (bpart g)⁻¹`, `∑_p ((g⁻¹)_(pi))² = (ᵗC C)_(ii) = ∑_p C_(pi)² ≥ C_(ii)² = exp(−2 α_i(g))`.

## The Gram determinant of the first columns of `g⁻¹`

- `det_gram_inv_cols`: let `g ∈ GL_(a+e)(ℝ)` and let `C` be the `(a+e) × a` matrix formed by the
  first `a` columns of `g⁻¹`. Then `det(ᵗC C) = exp(−2 ∑_(j<a) α_j(g))`. Proof: by `inv_val_eq`,
  `C = ᵗk · C'` with `C'` the first `a` columns of `(bpart g)⁻¹`, so `ᵗC C = ᵗC' C'`. Since
  `(bpart g)⁻¹` is upper triangular, the rows of `C'` below the first `a` vanish, so
  `ᵗC' C' = ᵗT T` for the upper triangular `a × a` block `T` of `(bpart g)⁻¹`. Its determinant is
  `(∏_j T_(jj))² = exp(−2 ∑_(j<a) α_j(g))` by `bpart_inv_diag`.

## `det(1 + ᵗx x) ≥ 1 + ∑ x²`

- `prod_one_add_ge`: `1 + ∑_(i∈s) f_i ≤ ∏_(i∈s) (1 + f_i)` for nonnegative `f`, by induction on
  the finite set `s`.
- `one_add_sum_sq_le_det`: for a real `d × a` matrix `x`,
  `1 + ∑_(l,j) x_(lj)² ≤ det(1 + ᵗx x)`. Proof: `ᵗx x` is positive semidefinite
  (Mathlib's `Matrix.posSemidef_conjTranspose_mul_self`), so `B = 1 + ᵗx x` is Hermitian. Each
  eigenvalue of `B` is `⟨v, Bv⟩` for a unit eigenvector `v` (Mathlib's
  `Matrix.IsHermitian.eigenvalues_eq`), hence at least `1`. The determinant is the product of
  the eigenvalues and the trace their sum (Mathlib's `det_eq_prod_eigenvalues` and
  `trace_eq_sum_eigenvalues`). Apply `prod_one_add_ge` to the eigenvalues minus one, and use
  `tr(B) = a + ∑_(l,j) x_(lj)²`.

## The determinant and reindexing

- `log_abs_det_eq_sum_alpha`: `log |det g| = ∑_i α_i(g)`. The unipotent factor has determinant
  `1`, the torus factor `exp(∑_i α_i(g))`, and the orthogonal factor absolute value `1`.
- `alpha_reindex_finCongr`: reindexing `GL_N` to `GL_N'` along an equality `N = N'`
  (`GeneralLinear.reindex (finCongr e)`) composes `α` with the corresponding cast of indices.

## Relation to the literature

These estimates replace Jacquet's Lemma 5.1 (*Archimedean Rankin–Selberg integrals*, 2009,
p. 33). That lemma bounds the diagonal Iwasawa coordinates `b_i` of a lower unipotent matrix
`v` above and below by products of the factors `1 + ‖X_j‖²`, where `X_j` are the
off-diagonal parts of the rows of `v`. Its proof uses the identity
`b_i² ⋯ b_n² = ‖(e_i ∧ ⋯ ∧ e_n) v‖²`. Here the individual coordinates are bounded by one row of `g` and
one column of `g⁻¹`, and only one Gram determinant, of the first columns of `g⁻¹`, is computed.
This arrangement was devised for the formalization.
