# Propagating vanishing block Fourier coefficients from `O(N)` to `GL_N(ℝ)`

Module: `Langlands.Representation.Archimedean.RealBlockFourierPropagation`, namespace
`Langlands.Archimedean.RealBlockPropagation`.

## Purpose and provenance

The standard module of an induction block of weight `m` at the coordinates `p, p + 1` is cut
out of a principal series by the vanishing of the block Fourier coefficients
`Φ_j(f)(g) = blockFourierCoefficient N p j f g` for `|j| < |m|` and **all** `g ∈ GL_N(ℝ)`
(module `StandardModule`, `realStandardModule`). Maps into such a module are controlled by
their values on `O(N)`. This module shows that, under the exponent condition that holds at
an induction block, vanishing on `O(N)` already implies vanishing everywhere.

Let `φ` be smooth with `IsExpEquivariant α φ` (module `RealBlockLeftDerivative`):
`φ(exp(diag x) u g) = exp(∑ αᵢ xᵢ) φ(g)` for upper unipotent `u`. Suppose
`α_p - α_{p+1} = m + 1`. For an induction block of weight `m`, the position characters
`sgn^{|m|+1} |·|^{t+|m|/2}` and `|·|^{t-|m|/2}` have `ρ`-shifted exponents with exactly this
difference `|m| + 1`.

This module is internal infrastructure for the proof of
`Langlands.Archimedean.RealCharacterPairFiltrationStatement`. The argument is an
elementary ODE uniqueness argument along paths in the Borel subgroup. It is derived here,
and the module makes no literature assertion, so it has no literature sources. The
definition `window` is internal notation.

## Declarations

### The window

- `window m : Finset ℤ` is the set of `j` with `|j| < m` and `j + m + 1` even, that is
  `j ∈ {1 - m, 3 - m, …, m - 1}`. `mem_window` states this characterization.
- `eq_of_mem_window_of_sub_two_not_mem`: if `j` is in the window and `j - 2` is not, then
  `j = 1 - m`. `eq_of_mem_window_of_add_two_not_mem`: if `j` is in the window and `j + 2` is
  not, then `j = m - 1`. Both are proved by `omega`, after writing `j + m + 1 = k + k`.

With `δ = m + 1`, these give `δ + j - 2 = 0` at `j = 1 - m` and `δ - j - 2 = 0` at `j = m - 1`.
These are the two coefficients through which the tridiagonal formula could leave the
window.

### A closed linear system on the window

- `window_ode a b c hF h0 ht`: let `F : ℤ → ℝ → ℂ` satisfy, for `j` in the window and all `t`,
  `F_j'(t) = a_j F_j(t) + b_j (m + 1 + j - 2) F_{j-2}(t) + c_j (m + 1 - j - 2) F_{j+2}(t)`,
  and `F_j(0) = 0`. Then `F_j(t) = 0` for all `t ≥ 0` and all `j` in the window.
  Proof: the vector `y(t) = (F_j(t))_{j ∈ window}` in the sup-normed space `window → ℂ` has
  `‖y'(t)‖ ≤ K ‖y(t)‖`, where `K` is the sum over the window of the norms of the three
  coefficients. A term involving `F_{j∓2}` with `j ∓ 2` outside the window has coefficient
  `0`, by the two lemmas above. Mathlib's Grönwall lemma
  `eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right` gives `y = 0` on `[0, t]`.

### Two paths in the Borel subgroup

Fix `h : p + 1 < N`, a smooth `φ` with `IsExpEquivariant α φ`, and
`hδ : α_p - α_{p+1} = m + 1`. The derivative along each path comes from
`hasDerivAt_blockFourierCoefficient_comp` (module `RealBlockLeftDerivative`), the
tridiagonal formula along a `C¹` path with `γ' = A γ`.

- `window_eq_zero_upperUnipotent_mul h hφ hα hδ u g h0`: if `Φ_j(φ)(g) = 0` for all `j` in the
  window, then `Φ_j(φ)(u g) = 0` for all `j` in the window and every upper unipotent `u`.
  The path is `γ(t) = (1 + t N') g` with `N' = u - 1` strictly upper triangular
  (`unipotentLine`, module `RealPrincipalSeriesDualityProof`). Its velocity `N' g` equals
  `A(t) γ(t)` with `A(t) = N' w(t)`, where `w(t) = (1 + t N')⁻¹` is upper unipotent. So `A(t)`
  is upper triangular with zero diagonal and `A(t)_{p,p+1} = N'_{p,p+1} = v`. The system is
  `F_j' = -(i v j / 2) F_j + (i v/4)(m + 1 + j - 2) F_{j-2} - (i v/4)(m + 1 - j - 2) F_{j+2}`,
  and `window_ode` applies at `t = 1`.
- `window_eq_zero_expDiagonal_mul h hφ hα hδ l g h0`: the same conclusion for
  `matrixExpUnit N (diag l) * g`, along `γ(t) = exp(t diag l) g` with velocity
  `diag(l) γ(t)` (Mathlib's `hasDerivAt_exp_smul_const'`; `C¹` by the Library's
  `contDiff_matExp`). With `x = l_p - l_{p+1}` the system is
  `F_j' = (∑ αᵢ lᵢ - (m+1) x/2) F_j + (x/4)(m + 1 + j - 2) F_{j-2} + (x/4)(m + 1 - j - 2) F_{j+2}`.

### The Iwasawa decomposition with positive diagonal

- `exists_expDiagonal_mul_upperUnipotent_mul_unitaryCompact g`: every `g ∈ GL_N(ℝ)` is
  `exp(diag l) (u k)` with `u` upper unipotent and `k ∈ O(N)`. Proof: write `g = b w` with
  `b` invertible upper triangular and `w` orthogonal (Library
  `exists_upperTriangular_mul_unitary`). Let `S = diag(sᵢ)` with `sᵢ = ±1` the sign of
  `b_ii`, so that `S² = 1` and `S` is orthogonal. Take `lᵢ = log |b_ii|`,
  `u = exp(diag l)⁻¹ b S = diag(|b_ii|⁻¹) b S`, which is upper triangular with diagonal
  `|b_ii|⁻¹ b_ii sᵢ = 1`, and `k = S w`. Then `exp(diag l) u k = b S S w = g`.

### Propagation

- `blockFourierCoefficient_window_eq_zero h hφ hα hδ hK g`: if `Φ_j(φ)(k) = 0` for every
  `k ∈ O(N)` and every `j` in the window, then `Φ_j(φ)(g) = 0` for every `g ∈ GL_N(ℝ)` and
  every `j` in the window. Proof: write `g = exp(diag l)(u k)`. Then
  `window_eq_zero_upperUnipotent_mul` passes from `k` to `u k`, and
  `window_eq_zero_expDiagonal_mul` passes from `u k` to `g`.

The indices `|j| < m` of the other parity are not covered here. For a principal series
whose position characters at `p, p + 1` have product sign `(-1)^{m+1}` at `-1`, as for an
induction block of weight `m`, those coefficients vanish identically by the sign
equivariance under `r_p(π) = s_p s_{p+1}`.
