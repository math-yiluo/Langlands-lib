# Rotation averages of products with tied block exponents

Lean module: `Langlands.Representation.Archimedean.RealInducedBlockInvariance`.

This module is part of the proof
of `RealStandardLanglandsQuotientStatement` (module `RealLargeLanglandsQuotientReduction`). It
shows that the rotation average along a block is block covariant with equal exponents when the
left exponents of the function at that block differ by exactly `2`. Unprefixed names below are in
the namespace `Langlands.Archimedean.RealInducedBlockInvariance`.

Notation follows `RealInducedBlockSlice.md` and `RealInducedBlockBound.md`. `GL_N(ℝ)` is
`Langlands.GeneralLinear N ℝ`. For `h : p + 1 < N`, `ia h = p` and `ib h = p + 1`. `r_p(θ)` is
`blockRotation N p θ`, and `Φ^p_j F (g) = ∫₀^{2π} F(r_p(θ) g) e^{−ijθ} dθ` is the Library's
`blockFourierCoefficient N p j F g`. `upperUnit h v = 1 + v E_{p,p+1}`, `diagVec h x y`,
`b(x, y, w) = blockB h x y w` and `IsBlockCovariant h a b F`
(`F(b(x, y, w) g) = e^{ax + by} F(g)`) are from `RealInducedBlockSlice`. `Slot`, `coeffs`,
`point` and `Slot.Disjoint` are from `RealInducedBlockBound`.
`RealBlockDerivative.IsExpEquivariant α φ` (Library module `RealBlockLeftDerivative`) means
`φ(exp(diag x) · u · g) = e^{Σ_i α_i x_i} φ(g)` for all real vectors `x`, upper unipotent `u` and
all `g`. A smooth function below is one with
`ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ φ`.

## Definitions

* `detFactor α slots = ∏_i e^{(α_{p_i} − 1)(x_i + y_i)}` over the slots `s_i` of the list, where
  `p_i = s_i.p` and `x_i, y_i` are the slot's coordinates.

## Results

* The imported
  `Langlands.Automorphic.OperatorRealization.eq_exp_mul_of_hasDerivAt`: if `F : ℝ → ℂ` has derivative `c F(t)` at every `t`, then
  `F(t) = e^{ct} F(0)`.
* `diagVec_ia`, `diagVec_ib`: `diagVec h x y` has entry `x` at `p` and `y` at `p + 1`.
* `upperUnit_zero`: `upperUnit h 0 = 1`.

For the next three results let `φ` be smooth with `IsExpEquivariant α φ` and
`α_p − α_{p+1} = 2`.

* `blockFourierCoefficient_zero_upperUnit_mul`:
  `Φ^p_0 φ ((1 + v E_{p,p+1}) g) = Φ^p_0 φ (g)` for all real `v` and all `g`.
* `blockFourierCoefficient_zero_expDiag_mul`:
  `Φ^p_0 φ (exp(diag(diagVec h x y)) g) = e^{(α_p − 1)(x + y)} Φ^p_0 φ (g)`.
* `isBlockCovariant_blockFourierCoefficient_zero` (**block invariance**):
  `IsBlockCovariant h (α_p − 1) (α_p − 1) (Φ^p_0 φ)`, i.e.
  `Φ^p_0 φ (b(x, y, w) g) = e^{(α_p − 1)(x + y)} Φ^p_0 φ (g)`.
* `coeffs_point_mul` (**several blocks**): let `φ` be smooth with `IsExpEquivariant α φ`, and let
  `slots` be a list of pairwise disjoint slots (`slots.Pairwise Slot.Disjoint`) with mode
  `s.j = 0` and `α_{s.p} − α_{s.p + 1} = 2` for every slot `s`. Then for all `g`:

  `coeffs slots φ (point slots · g) = detFactor α slots · coeffs slots φ g`.

## Statement

`Langlands.Archimedean.RealInducedBlockInvarianceStatement` (outside the namespace above) is the
proposition form of `coeffs_point_mul`, quantified over `N`, smooth `φ`, `α` with
`IsExpEquivariant α φ`, the slots and `g`. `Langlands.Archimedean.realInducedBlockInvariance`
proves it by `coeffs_point_mul`.

This module imports the modules `RealInducedBlockContour`, `RealInducedBlockSlice` and
`RealInducedBlockBound` (each with its own Markdown file). The last of
them states and proves `Langlands.Archimedean.RealInducedBlockBoundStatement`.

## Proofs

The scalar ODE theorem is reused from `Automorphic.CuspidalAdmissible.CentralEigen`.
Its proof observes that `t ↦ e^{−ct} F(t)` has derivative `0` everywhere, so it is constant
(Mathlib's `is_const_of_deriv_eq_zero`).

The two derivative computations use the Library's tridiagonal formula
`RealBlockDerivative.hasDerivAt_blockFourierCoefficient_comp`. For a `C¹` path `γ` in `GL_N(ℝ)`
with `γ'(s) = A γ(s)`, `A` upper triangular, it expresses the derivative of
`s ↦ Φ^p_j φ (γ(s))` through `Φ^p_j`, `Φ^p_{j−2}` and `Φ^p_{j+2}` at `γ(s)`. The coefficients of
`Φ^p_{j−2}` and `Φ^p_{j+2}` contain the factors `α_p − α_{p+1} + j − 2` and
`α_p − α_{p+1} − j − 2`. Both vanish for `j = 0` and `α_p − α_{p+1} = 2`, so
`(Φ^p_0 φ ∘ γ)' = c · (Φ^p_0 φ ∘ γ)` with
`c = Σ_i α_i A_ii − (A_pp − A_{p+1,p+1})`.

* `blockFourierCoefficient_zero_upperUnit_mul`: take `E = v E_{p,p+1}` and
  `γ(t) = (1 + tE) g`. Since `E² = 0`, `γ'(t) = E g = E γ(t)`. `E` is upper triangular with zero
  diagonal, so `c = 0` and `t ↦ Φ^p_0 φ (γ(t))` is constant. Compare `t = 1` and `t = 0`.
* `blockFourierCoefficient_zero_expDiag_mul`: take `L = diag(diagVec h x y)` and
  `γ(t) = exp(tL) g`, with `γ'(t) = L γ(t)` (Mathlib's `hasDerivAt_exp_smul_const'`) and `γ`
  of class `C¹` (Library `RealJacquetFrobenius.contDiff_matExp`). Here
  `c = α_p x + α_{p+1} y − (x − y) = (α_p − 1)(x + y)` because `α_{p+1} = α_p − 2`
  (`RealInducedBlockSlice.sum_mul_diagVec`). `eq_exp_mul_of_hasDerivAt` at `t = 1` gives the
  claim.
* `isBlockCovariant_blockFourierCoefficient_zero`: by definition
  `b(x, y, w) = exp(diag(diagVec h x y)) · upperUnit h (w e^{−x})`; apply the two previous
  results in turn.
* `coeffs_point_mul` is an induction on the list. The empty list is trivial. For `s :: rest`,
  write `G = coeffs rest φ` and `Y = point rest`; then
  `coeffs (s :: rest) φ (point (s :: rest) g) = Φ^{s.p}_0 G (b_s Y g)`.
  1. `Φ^{s.p}_0 G = coeffs rest (Φ^{s.p}_0 φ)` (`RealInducedBlockBound.blockFourierCoefficient_coeffs`,
     since `s` is disjoint from all of `rest` and `φ` is continuous). By block invariance
     `Φ^{s.p}_0 φ` is block covariant at `s` with exponents `(α_{s.p} − 1, α_{s.p} − 1)`, and
     `RealInducedBlockBound.isBlockCovariant_coeffs` carries this to `coeffs rest (Φ^{s.p}_0 φ)`.
     This removes `b_s` with the factor `e^{(α_{s.p} − 1)(x_s + y_s)}`.
  2. It remains to show `Φ^{s.p}_0 G (Y g) = detFactor α rest · Φ^{s.p}_0 G (g)`. Inside the
     integral, `r_{s.p}(θ) Y = Y r_{s.p}(θ)` (`RealInducedBlockBound.blockRotation_mul_point`),
     and the induction hypothesis at the point `r_{s.p}(θ) g` gives
     `G(Y r_{s.p}(θ) g) = detFactor α rest · G(r_{s.p}(θ) g)`.
  3. `detFactor α (s :: rest)` is the product of the two factors.

## Use

By the Library's `RealBlockDerivative.isExpEquivariant_of_mem_principalSeries`, a vector of a
principal series with exponents `τ` satisfies `IsExpEquivariant` with
`α_i = τ_i + (N − 1)/2 − i`. If `u` has exponents `τ` and `h` has exponents `−τ`, the product
`g ↦ u(g) h(g)` has exponents `α_i = N − 1 − 2i`, so `α_p − α_{p+1} = 2` at every block. Block
invariance then says that the rotation average of such a product over a block depends on the
block coordinates only through `e^{(α_p − 1)(x + y)}`. This module does not itself state the
statement about products; it is intended, together with the bound of `RealInducedBlockBound`,
for the pairing of a principal-series vector with a dual vector in the proof of
`RealStandardLanglandsQuotientStatement`.

## Provenance

This is derived, internal infrastructure for the proof of `RealStandardLanglandsQuotientStatement`;
it states no literature result. It is
the `j = 0` case of the Library's tridiagonal derivative formula, where the coefficients of the
neighbouring modes vanish, integrated along one-parameter subgroups.
