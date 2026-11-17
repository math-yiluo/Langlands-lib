# Minors of matrices as matrices of exterior powers

Lean module: `Langlands.Representation.Archimedean.ComplexJacquetTranslationMinors`, namespace
`Langlands.Archimedean.JacquetTranslation`.

This module holds no statement definition. It provides the matrix algebra and calculus of
`k × k` minors used by the proof of `ComplexJacquetTranslationStatement`
(module `ComplexJacquetTranslationProof`). All content is internal.

## Subsets and minors

- `Sub n k` is `Set.powersetCard (Fin n) k`, the `k`-element subsets of `Fin n`. For `S : Sub n k`,
  `(S : Finset (Fin n)).card = k` is `S.prop`. `enum S : Fin k ↪o Fin n` is the increasing
  enumeration of `S` (Mathlib `Set.powersetCard.ofFinEmbEquiv`).
- `extBasis n k` is the basis `e_S` of `Λ^k ℂ^n` indexed by `Sub n k` (Mathlib
  `Module.Basis.exteriorPower`).
- `minorMat A : Matrix (Sub n k) (Sub n k) ℂ` is the matrix of `Λ^k A` in the basis `e_S`.
  - `minorMat_apply`: `minorMat A S T` is the determinant of the `k × k` matrix
    `(A (enum S i) (enum T j))_{i j}`, the minor of `A` with rows `S` and columns `T`.
  - `minorMat_mul`: `minorMat (A * B) = minorMat A * minorMat B` (the Cauchy–Binet formula;
    here it is functoriality of `Λ^k` together with `LinearMap.toMatrix_comp`).
  - `minorMat_one`, `minorMat_transpose` (`minorMat Aᵀ S T = minorMat A T S`),
    `minorMat_map_conj` (entrywise conjugation commutes with minors).
- `wt S = ∑_{s ∈ S} s` (as natural numbers) is the weight of a subset.
  `sum_enum`, `prod_enum` and `mem_iff_exists_enum` translate between `S` and its enumeration.

## Minors of upper triangular matrices

Let `b` be upper triangular (`b i j = 0` for `j < i`).

- `minorMat_upper_ne_zero`: if `minorMat b S T ≠ 0` then `wt S ≤ wt T`, and `wt S = wt T`
  forces `S = T`. Proof: some term `∏_i b (enum S (σ i)) (enum T i)` of the Leibniz expansion is
  nonzero, so `enum S (σ i) ≤ enum T i` for all `i`; summing gives `wt S ≤ wt T`, and equality
  of the sums forces equality of all terms, hence `S = T`.
- `minorMat_upper_self`: `minorMat b S S = ∏_{s ∈ S} b s s` (`Matrix.det_of_isUpperTriangular`).
- `minorMat_diagonal`: the minors of a diagonal matrix `diag(v)` are `∏_{s ∈ S} v s` on the
  diagonal and `0` off it (apply the previous lemmas to `diag(v)` and its transpose).
- `lowSub n k hk` (for `k ≤ n`) is the set `{j | n ≤ j + k}` of the last `k` positions
  (`mem_lowSub`). `minorMat_upper_low`: the row `lowSub` of `minorMat b` is
  `∏_{r ∈ lowSub} b r r` at `lowSub` and `0` elsewhere (any other column set `U` contains some
  `u < n - k`, and the column `u` of the minor vanishes below the diagonal).

## Holomorphic and antiholomorphic minors

- `phi anti y` is `y` (`anti = false`) or its entrywise conjugate (`anti = true`); it is
  multiplicative (`phi_mul`, `phi_one`).
- `mm anti y = minorMat (phi anti y)`: the holomorphic or antiholomorphic minors.
  `mm_mul`, `mm_one`; `contDiff_mm` (each entry is a real-smooth function of the matrix) and
  `contMDiff_mm` (the same on `GL_n(ℂ)` with its matrix chart).

## Right derivatives of minors

- `Dco anti U T X` is the real derivative at `1` of `y ↦ mm anti y U T` in the direction `X`:
  the matrix coefficient of the derived action of `X` on `Λ^k`.
- `rightDerivative_mm`: for `g ∈ GL_n(ℂ)`,
  `R(X)(g ↦ mm anti g S T)(g) = ∑_U mm anti g S U · Dco anti U T X`. Proof: by `mm_mul`,
  `y ↦ mm anti (g y) S T` equals `y ↦ ∑_U mm anti g S U · mm anti y U T`; differentiate at `1`
  (`mfderiv_eq_fderiv_of_eq_comp`, `HasFDerivAt.fun_sum`).
- `hasDerivAt_mm_line`: `Dco anti U T X` is the derivative at `0` of `t ↦ mm anti (1 + tX) U T`.
- `mm_line_low` and `Dco_low`: for upper triangular `X`, the row `lowSub` of `mm anti (1 + tX)` is
  `∏_{r ∈ lowSub} (1 + t · phi anti X r r)` at `lowSub` and `0` elsewhere, so
  `Dco anti lowSub U X = ∑_{r ∈ lowSub} phi anti X r r` if `U = lowSub` and `0` otherwise
  (`HasDerivAt.fun_finsetProd` and uniqueness of derivatives).
