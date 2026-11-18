# The gauge estimate for uniformly regular real Whittaker functions

Helper module for the convergence part of the real local Rankin–Selberg theory (Task 7400,
towards `Langlands.Global.RankinSelbergGlobal.RealPlaceFunctionalEquationStatement`).
Authored by Worker 823. Every declaration is proved. The module uses no axioms beyond
Lean's standard ones (`propext`, `Classical.choice`, `Quot.sound`).

All declarations are in the namespace
`Langlands.Global.RankinSelbergGlobal.RealWhittakerGauge`. Throughout, `G = GL_(r+1)(ℝ)`,
`a ∈ ℝˣ` is an additive parameter, `regularFunctions r a` and `iteratedRightDerivative r Xs W`
are the accepted definitions of the module `RealLocalWhittakerProperties`, and
`realMatrixHeight g = ∑_(i,j) (|g_ij|² + |(g⁻¹)_ij|²)` comes from `RealLocalWhittakerModel`.
`torus y = diag(exp y_0, …, exp y_r)` is from the module `RealIwasawa`, and `k` ranges over the
orthogonal group `unitaryCompact ℝ (r+1)`.

## Main result

`exists_gauge_bound`. Let `W : G → ℂ` satisfy

- `hreg`: every iterated right derivative `iteratedRightDerivative r Xs W` lies in
  `regularFunctions r a` (smooth, left `(N, ψ_a)`-equivariant, polynomially bounded); and
- `hgrowth`: there is one exponent `N` such that for every derivative word `Xs` there is
  `C ≥ 0` with `‖iteratedRightDerivative r Xs W g‖ ≤ C · realMatrixHeight(g)^N` for all `g`.

Then there is `N'` (in fact `N' = 2N`) such that for every `M : ℕ` there is `C ≥ 0` with

`‖W(torus y · k)‖ ≤ C · exp(−M · ∑_(i<r) max(y_i − y_(i+1), 0) + N' · ∑_j |y_j|)`

for all `y ∈ ℝ^(r+1)` and all orthogonal `k`.

The two hypotheses have the same shape as the two conjuncts in Worker 771's statement
`RealUniformWhittaker.HasUniformDerivativeGrowth` and the regularity part of
`realUniformWhittakerRegularity` (candidate 660d932e). This module states them as explicit
hypotheses and does not depend on that candidate.

This is the real case of the gauge estimate of Jacquet, *Archimedean Rankin–Selberg
integrals* (2009), Proposition 3.1 (pp. 15–16): a Whittaker function decays rapidly in each
simple-root coordinate `y_i − y_(i+1) → +∞`. The proof below follows the classical argument with derivatives along
conjugated root directions, arranged so that only one common growth exponent is needed.

## Proof outline

### One-parameter subgroups and the character (part 1)

- `exp_smul_of_mul_self_eq_zero`: if `Y² = 0` then `exp(sY) = 1 + sY`.
- `rootMatrix i = E_(i,i+1)` with `rootMatrix_mul_self`. `conjRoot g i = g⁻¹ E_(i,i+1) g`
  with `conjRoot_mul_self`.
- `mul_matrixExpUnit_conjRoot`: `g · exp(s · conjRoot g i) = exp(s E_(i,i+1)) · g`.
- `matrixExpUnit_rootMatrix_mem`: `exp(s E_(i,i+1))` is upper unipotent.
- `realWhittakerCharacter_matrixExpUnit_rootMatrix`: the standard character takes the value
  `realScaledCharacter a s` on it, and `hasDerivAt_realScaledCharacter` gives the derivative
  `2π a I` (with `I = √−1`) of that character at `0`.

### The one-step identity (part 2)

- `rightDerivative_conjRoot`: for `F ∈ regularFunctions r a`,
  `R(conjRoot g i) F (g) = 2π a I · F(g)`. The proof differentiates
  `s ↦ F(g · exp(s · conjRoot g i)) = ψ_a(s) · F(g)` at `s = 0`, using the Library lemma
  `hasDerivAt_mul_matrixExpUnit_smul` and uniqueness of derivatives.
- `rightDerivativeHom`, `rightDerivative_eq_sum`: the right derivative is additive in the
  direction, so `R(X) F = ∑_(p,q) X_pq · R(E_pq) F`. `norm_rightDerivative_le` gives the
  resulting pointwise bound.
- `rootSize g i = ∑_(p,q) |conjRoot g i p q|`.
- `exists_bound_list`: by induction on a list `is` of simple roots, for every word `Ys`
  there is `C ≥ 0` with
  `‖iteratedRightDerivative r Ys W g‖ ≤ C · ∏_(i ∈ is) rootSize g i · realMatrixHeight(g)^N`.
  At each step the one-step identity, applied to `iteratedRightDerivative r Ys W` (which is
  regular by `hreg`), divides by `2π|a|`. It expands the derivative along `conjRoot g i` into
  the elementary derivatives `E_pq :: Ys`, and the induction hypothesis bounds these with the
  same exponent `N`. Because the exponent stays fixed, the induction needs the uniform
  hypothesis `hgrowth`.
- `exists_list_prod`: every product `∏_i f(i)^(m_i)` is the product of `f` along some list.

### Entries on `torus y · k` (part 3)

- `conjRoot_apply`: `conjRoot g i p q = (g⁻¹)_(p,i) · g_(i+1,q)`.
- `abs_unitary_entry_le`, `abs_unitary_inv_entry_le`: orthogonal matrices and their
  inverses have entries of absolute value at most `1` (Mathlib's
  `entry_norm_bound_of_unitary`).
- `torus_mul_val_apply`, `torus_mul_inv_val_apply`: the entries of `torus y · k` and of its
  inverse.
- `abs_conjRoot_torus_mul_le`: `|conjRoot (torus y · k) i p q| ≤ exp(y_(i+1) − y_i)`. Hence
  `rootSize_torus_mul_le`: `rootSize (torus y · k) i ≤ (r+1)² · exp(y_(i+1) − y_i)`.
- `sq_exp_mul_le`, `realMatrixHeight_torus_mul_le`:
  `realMatrixHeight(torus y · k) ≤ 2(r+1)² · exp(2 ∑_j |y_j|)`. Then
  `realMatrixHeight_torus_mul_pow_le` gives the `N`-th power with exponent `2N`.
- `rootSize_pow_le`, `prod_rootSize_pow_le`: let `S` be the set of `i` with
  `y_i − y_(i+1) ≥ 0`, and use the exponent `M` for `i ∈ S` and `0` otherwise. Then
  `∏_i rootSize^(m_i) ≤ ((r+1)^(2M))^r · exp(−M ∑_i max(y_i − y_(i+1), 0))`.

### Assembling the estimate

For each of the finitely many subsets `S` of the simple roots, `exists_list_prod` and
`exists_bound_list` (with the empty word) give a constant `C_S`. The final constant is
`(∑_S C_S) · ((r+1)^(2M))^r · (2(r+1)²)^N`, and the bound at `torus y · k` uses the subset
`S` determined by `y`.
