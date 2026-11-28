# Line rotations of antihermitian forms over a division algebra

Module `Langlands.GroupScheme.Quaternionic.SkewLineRotation`, namespace
`Langlands.GroupScheme.Quaternionic.FirstKindInvolution.LineRotation`.

Let `A` be a division algebra over a field `K`, `τ` an involution of the first kind of `A`, and
`G` an `n × n` Gram matrix with form `h(x, y) = τ.sesqForm G x y = ∑ x i G i j τ(y j)` on row
vectors. Matrices act on rows on the right, `v ↦ v ᵥ* M`.

## Line matrices

For a row `a` with `c = h(a, a)` and `e ∈ A`,
`lineMatrix τ G a e = 1 + vecMulVec (G *ᵥ (τ ∘ a)) ((c⁻¹ (e - 1)) • a)`.

* `vecMul_lineMatrix`: `v ᵥ* lineMatrix τ G a e = v + (h(v, a) c⁻¹ (e - 1)) • a`.
* `vecMul_lineMatrix_of_orthogonal`: if `h(v, a) = 0` then `v` is fixed.
* `vecMul_lineMatrix_self`: if `c ≠ 0` then `a ↦ e • a`.
* `lineMatrix_one` gives the identity matrix for parameter `1`. For `c ≠ 0`, `lineMatrix_mul`
  gives `lineMatrix a e * lineMatrix a e' = lineMatrix a (e e')`. With `e ≠ 0`,
  `lineMatrix_mul_inv` and `lineMatrix_inv_mul` give the inverse with parameter `e⁻¹`.

## Invariance of the form

Assume `G` is antihermitian (`τ.IsAntihermitian G`). Then `τ(c) = -c`
(`map_sesqForm_self_eq_neg`).

* `lineParameter_identity`: if `c ≠ 0`, `τ(c) = -c` and `e c τ(e) = c`, then
  `k = c⁻¹ (e - 1)` satisfies `τ(k) - k + k c τ(k) = 0`; multiplying by `c` on both sides gives
  `c - e c τ(e)`.
* `sesqForm_vecMul_lineMatrix`: under `c ≠ 0` and `e c τ(e) = c`, the line matrix preserves `h`.
  The expansion of `h(v + β k a, w + γ k a)` differs from `h(v, w)` by `β (τ(k) - k + k c τ(k)) τ(γ)`.
* `mul_mul_matrix_eq_of_sesqForm`: a matrix preserving `h` satisfies `M G ᵗM^τ = G`, by evaluating
  on standard basis rows (`mul_mul_matrix_apply`).

## Unitary reflections

`reflection_spec`: let `h(x, x) = h(y, y)` and put `s = h(x, x - y)`. If `τ(s) ≠ s`, then:

* `h(x - y, x - y) = s - τ(s)` is nonzero;
* `e = τ(s) s⁻¹` satisfies `e h(x - y, x - y) τ(e) = h(x - y, x - y)`;
* `x ᵥ* lineMatrix τ G (x - y) e = y`, since `s (s - τ s)⁻¹ (τ(s) s⁻¹ - 1) = -1`.

## Square roots of parameters

Assume a function `N : A → K` with `x τ(x) = N(x)` (as scalars). Then `N(t) = t²` on scalars,
`N(1) = 1`, `τ(x) x = N(x)`, `N(τ x) = N(x)`, `N(x y) = N(x) N(y)`, and `N(x) ≠ 0` for `x ≠ 0`
(`norm_algebraMap`, `norm_one`, `map_mul_self`, `norm_map`, `norm_mul`, `norm_ne_zero`).
`add_map_eq` gives `y + τ(y) = N(1 + y) - 1 - N(y)`, so `τ(y) = y` forces `y` to be a scalar in
characteristic zero (`mem_range_of_map_eq`).

Assume further that `K` has characteristic zero, every element or its negative is a square,
and sums of two squares are squares.

* `isSquare_norm`: `N(y)` is a square. Otherwise `N(y) = -w²`, the binary form
  `N(t + y) = t² + β t + N(y)`, `β = y + τ(y)`, has discriminant `β² + 4 w²`, a square, so it has a
  root `t₀`; then `(t₀ + y) τ(t₀ + y) = 0`, so `y = -t₀` is a scalar and `N(y) = t₀²`.

Assume finally that `-1` is not a square.

* `exists_sqrt_parameter`: if `c ≠ 0`, `τ(c) = -c` and `e c τ(e) = c`, there is `f` with
  `f c τ(f) = c` and `f² = e`. First `N(e)² = 1` and `N(e)` is a square, so `N(e) = 1`, hence
  `τ(e) = e⁻¹` and `e` commutes with `c`. If `e = -1`, take `f = r⁻¹ c` with `N(c) = r²`, using
  `c² = -N(c)`. Otherwise take `f = r⁻¹ (1 + e)` with `N(1 + e) = r²`, using
  `(1 + e)² = N(1 + e) e`.

## Provenance (derived)

The line matrices are the quasi-symmetries of a unitary group (J. Dieudonné, *La géométrie des
groupes classiques*), written for row vectors and antihermitian Gram matrices. The square-root
computation is the half-angle formula in the norm-one torus of `K(c)`. The module is internal to
the Library.
