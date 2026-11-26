# Normalized compact averages from opposite-cell contraction

Fix a rank `n = r + 1`, a real block list `ds`, `ε > 0` and the contracting diagonal
`d_ε = contractionDiagonal n ε` with entries `ε^i` (`RealOppositeDilation`).

## Definitions

* `contractionArguments n ε` are the diagonal entries `ε^i` as units, and
  `contractionCharacter n ds ε` is the inducing character of the standard module of `ds` on
  `d_ε`; it is nonzero (`contractionCharacter_ne_zero`).
* `oppositeMass f₀ = ∫_{N_n} f₀(uᵀ) du` for the entry Lebesgue measure `realEntryLebesgue n`.
* `averageFactor c ds ε n = c · ε^D · contractionCharacter n ds ε`, where `D` is
  `contractionDegree n` (the real Jacobian of the contraction of upper entries) and `c` the
  constant of `RealModulusOpenCell`; `averageScale c f₀ ε = (oppositeMass f₀)⁻¹ ·
  (averageFactor c ds ε n)⁻¹`.
* `contractedPair f f₀ x ε u = f₀(uᵀ) · dualSection f x ((contraction u)ᵀ)`, where
  `contraction` scales the entry `(i, j)` by `ε^(j - i)` and `dualSection` is the dual
  compact probe of `RealCompactDualProbe`.
* `inverseWeight f` is the continuous function `k ↦ f(k⁻¹)` on `O(n)`.

## Statement

`RealNormalizedCompactAverageStatement`: for every `r` there is `c > 0` such that for every
`ds`, `a`, every `IsRealWhittakerIntertwiner r ds a B`, every standard vector `f₀` with
`oppositeMass f₀ ≠ 0` and every `ε > 0` there is a linear operator `A` on the standard module
`Automorphic.realStandardKFinite (r + 1) ds` with

1. for every `f` and orthogonal `x`: `contractedPair f f₀ x ε` is integrable and
   `(A f)(x) = (oppositeMass f₀)⁻¹ ∫_{N} contractedPair f f₀ x ε u du`;
2. `(A f)(y) = averageScale c f₀ ε · ∫_{O(n)} f(k⁻¹) f₀(y k d_ε) dk` for all `y`;
3. `B (A f) y = averageScale c f₀ ε · ∫_{O(n)} f(k⁻¹) (B f₀)(y k d_ε) dk` for all `y`.

`realNormalizedCompactAverage` proves it.

## Proof

* `inverseWeight f` has finite-dimensional span of left translates, since `f` is
  `O(n)`-finite and inversion turns right translates into left translates
  (`inverseWeight_finite`).
* The exact compact projection theorem `realExactCompactProjection`, applied to the weight
  `inverseWeight f`, the vector `f₀` and the translation `d_ε`, gives for each `f` a standard
  vector `P f` satisfying (2) and (3) up to the scalar. These values determine `P f`, so `P`
  is linear by linearity of the integral; `A` is `averageScale c f₀ ε · P`.
* At an orthogonal point `x`, left invariance of the Haar measure rewrites the average as
  `∫ f(k⁻¹ x) f₀(k d_ε) dk`; the dual probe identity of `realCompactDualProbe` replaces it by
  `∫_{O(n)} dualSection f x (k) f₀(k d_ε) dk`. The product
  `y ↦ dualSection f x (y) f₀(y d_ε)` is smooth and covariant for the modulus character
  (the dual characters multiply to the modulus, `principalSeriesCharacter_dual_mul`), so
  `realModulusOpenCell` turns the compact integral into `c` times an absolutely convergent
  integral over the opposite cell.
* The substitution `u ↦ contraction u` has Jacobian `ε^D` (`map_contraction`), and
  `f₀((contraction u)ᵀ d_ε) = contractionCharacter · f₀(uᵀ)` because
  `(contraction u)ᵀ = d_ε uᵀ d_ε⁻¹` (`transpose_contraction`). Dividing out
  `averageFactor` and `oppositeMass f₀` gives (1).

This is the real counterpart of the Library's `ComplexNormalizedCompactAverage`. It connects
the compact projection of a Whittaker intertwiner with the opposite-cell approximation used in
`RealWhittakerApproximateIdentity`.
