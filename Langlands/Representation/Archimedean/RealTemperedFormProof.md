# Invariant form data for tied real standard modules

Author: Worker 378. Module `Langlands.Representation.Archimedean.RealTemperedFormProof`. Its auxiliary
declarations are in the namespace `Langlands.Archimedean.RealTemperedForm`. The final theorem is
`Langlands.Archimedean.realTemperedForm`. The module proves the Library statement
`Langlands.Archimedean.RealTemperedFormStatement` (module `RealTemperedCommutantReduction`) for
Task 7625. It changes no published file.

The proof is derived here and follows no specific literature source. Its Lie identity uses a
"dual partner", like the Library's complex analogue `ComplexTemperedComplement.unitaryForm_lie_add`.
It does not use the Langlands quotient theorem, the Langlands classification for lists with ties, or
`RealTemperedStandardIrreducibleStatement`.

Notation. `GL_n(ℝ)` is `Langlands.GeneralLinear n ℝ`, and `O(n)` is `unitaryCompact ℝ n`.
`K(ds) = RealTemperedCommutantReduction.KF n ds` is the space of `O(n)`-finite functions of
`realStandardModule n ds`. `dk` is the normalized Haar measure `haarK n` on `O(n)` (module
`RealPrincipalSeriesDualityProof`). `R_X` is the right derivative
`rightDerivative (matrixModel ℝ n) X` along a real matrix `X`. `Φ^p_j = blockFourierCoefficient n p j`
is the `j`-th Fourier coefficient along the rotations of the block `p, p + 1`. `coeffs L F` is the
iterated coefficient `Φ^{p_1}_{j_1} ⋯ Φ^{p_r}_{j_r} F` along a list `L` of slots (module
`RealInducedBlockBound`). `withModes L J`, `zeroModes L`, `modeLists D r` and `HasDegree` come from
`RealInducedTorusCore`. `IsBlockFrobData`, `blockFrobMap` and `tailMultiplier` come from
`RealBlockFrobeniusMap` and `RealBlockMultiplier`, and `detPow n s g = |det g|^s` from
`RealLinkedJacquetStages`.

## Main theorem

```lean
theorem Langlands.Archimedean.realTemperedForm : RealTemperedFormStatement
```

Unfolded, it says the following. Let `n` be a natural number and `ds` a list of real blocks with
`realRank ds = n` whose real exponents `realBlockExponent` are all equal. Then
`HasTemperedForm n ds` holds:

* `K(ds)` is nontrivial;
* there is a form `B : K(ds) →ₗ[ℂ] K(ds) →ₗ⋆[ℂ] ℂ`, linear in the first argument and
  conjugate-linear in the second, such that:
  * `B v v = 0` implies `v = 0`;
  * `B (k·v) (k·w) = B v w` for `k ∈ O(n)` acting by `realStandardRep`;
  * for each real matrix `X` there is `c ∈ ℂ` with `B (X·v) w + B v (X·w) = c · B v w` for all
    `v, w`, where `X` acts through `realStandardLie n ds (1 ⊗ₜ X)`.

Nontriviality is the Library theorem `realStandardNontrivial`. The rest of this file describes the
form. Let `r` be the common real exponent; for `ds = []` any `r` works.

## Section `Coefficients`: Parseval along blocks

* `coeffs_const_mul`, `coeffs_eq_mul_of_eqOn`, `blockFourierCoefficient_eq_mul_of_eqOn`: if
  `G = c F` on `O(N)`, the block and iterated coefficients of `G` are `c` times those of `F` on
  `O(N)`. This holds because `O(N)` is stable under left multiplication by block rotations.
* `blockFourierCoefficient_coeffs_eq_mul`: a relation `Φ^p_j G = c Φ^p_j F` on `O(N)` passes to
  `Φ^p_j (coeffs L G) = c Φ^p_j (coeffs L F)` when every slot of `L` is disjoint from the block
  `p, p + 1`. The proof commutes `Φ^p_j` with `coeffs L` using the Library's
  `blockFourierCoefficient_coeffs`.
* `RealSwapFLanding.blockFourierCoefficient_conj` and `coeffs_withModes_conj`: `Φ_j (conj F) = conj (Φ_{-j} F)`,
  and the iterated version with negated modes.
* `coeffs_zeroModes_mul_conj_eq_sum` (**pointwise Parseval**). Let `L` be pairwise disjoint, let `u`
  be continuous, `O(N)`-finite and of degree `≤ D` along `L`, and let `v` be continuous. For
  `k ∈ O(N)`,
  `coeffs (zeroModes L) (u · conj v) k = (2π)^{-|L|} Σ_{J ∈ modeLists D |L|} c_J(u)(k) · conj(c_J(v)(k))`,
  with `c_J = coeffs (withModes L J)`. It follows from the Library's `coeffs_zeroModes_mul_eq_sum`
  applied to `u` and `conj v`, together with `coeffs_withModes_conj`.
* `integral_eq_inv_mul_coeffs_zeroModes`:
  `∫_{O(N)} G dk = (2π)^{-|L|} ∫_{O(N)} coeffs (zeroModes L) G dk` for continuous `G`. This is a
  rewriting of the Library's `integral_coeffs_zeroModes`.
* `eq_zero_of_integral_eq_zero_of_nonneg`: a continuous `Q ≥ 0` with `∫_{O(N)} Q = 0` vanishes on
  `O(N)`. The proof uses `integral_eq_zero_iff_of_nonneg` and `Continuous.ae_eq_iff_eq` for the
  Haar measure.

## Section `Calculus`

`contMDiff_conj` and `rightDerivative_conj`: `g ↦ conj (A g)` is smooth if `A` is, and
`R_X (conj A) = conj (R_X A)` for real `X`. The proof uses `rightDerivative_eq_fderiv`, the
extension `unitsExtension` to all matrices, and `fderiv_star`.

## Section `Partner`: the dual partner and the Lie identity

* `detPow_mul_conj_principalSeriesCharacter`: on the diagonal torus,
  `|det(diag a)|^s · conj(δ_{χ'}(a)) = δ_{χ''}(a)` for `χ''_i(x) = conj(χ'_i(x)) |x|^s`.
* `partner_mem` (**dual partner**): if `χ_i(x) · conj(χ'_i(x)) · |x|^s = 1` for every position
  `i < n` and every `x`, then for `v` in the principal series of `χ'` the function
  `P(v)(g) = |det g|^s · conj(v(g))` lies in the principal series of `χ⁻¹`. Smoothness uses
  `contMDiff_detPow` and `contMDiff_conj`. The transformation law uses the formula above,
  `detPow_mul` and `detPow_of_mem_upperUnipotent`.
* `integral_lie_conj` (**Lie identity of the pairing**). Under the same hypothesis, with `χ` nowhere
  zero, `f` in the principal series of `χ` and `R_X f`, `R_X v` continuous,
  `∫ (R_X f) conj v dk + ∫ f conj (R_X v) dk = -c · ∫ f conj v dk`, where
  `c = R_X(|det|^s)(1)` depends only on `X` and `s`. The proof: `f · P(v)` is modulus-equivariant
  (Library `isModulusEquivariant_mul`), so `∫_{O(n)} R_X(f · P(v)) = 0`
  (`integral_rightDerivative_eq_zero`). On `O(n)`, the product rule (`rightDerivative_mul_fun`),
  `rightDerivative_conj`, `rightDerivative_detPow` and `detPow_of_mem_unitaryCompact`
  (`|det k|^s = 1`) give
  `R_X(f · P(v))(k) = (R_X f)(k) conj v(k) + c f(k) conj v(k) + f(k) conj (R_X v)(k)`.

## Section `Lists`: replacing induction blocks by characters

* `cLow d = charData ⟨(ℓ + 1) mod 2⟩ (t - ℓ/2)` and `cHigh d = charData 0 (t + ℓ/2)`, for an induction
  block `d` of exponent `t` and weight `ℓ = |d.weight|`.
* `repl` keeps a character and an induction block of weight `0`. It replaces an induction block `d`
  of nonzero weight by `[character (cLow d), character (cHigh d)]`. Let `es = ds.flatMap repl`; it has
  the same rank (`realRank_flatMap_repl`).
* `charFun_mul_conj`: `charFun e t x · conj(charFun e t' x) · |x|^{-2r} = 1` when
  `t + conj t' = 2r` (using `Complex.cpow_conj`, the argument of `|x|` being `0`).
* `position_rel`: if every real exponent of `ds` is `r`, then for `i < realRank ds` the lists `ds` and
  `es` have the same sign at `i`, and their exponents satisfy `t_i(ds) + conj(t_i(es)) = 2r`. An
  induction block `d` has the position exponents `(t + ℓ/2, t - ℓ/2)`, and its replacement has
  `(t - ℓ/2, t + ℓ/2)`. Then `(t ± ℓ/2) + conj(t ∓ ℓ/2) = t + conj t = 2 Re t = 2r`. The same
  computation covers characters and blocks of weight `0`.
* `position_char`: hence `χ^{ds}_i(x) · conj(χ^{es}_i(x)) · |x|^{-2r} = 1` for the position characters
  (`realPositionCharacter_eq_charFun`). This is the hypothesis of `partner_mem` with `s = -2r`.

## Section `Chain`: a chain of block Frobenius maps

* `tailMultiplier_one_eq`: the tail multiplier with sign `1` takes natural-number values
  `tailNat ℓ ε j = C(⌊|j|/2⌋ + ⌊(ℓ - 1 + ε)/2⌋, ℓ)`.
* `ChainData n b Z X` bundles the following data:
  * a linear map `T : K(Z) → K(X)` commuting with every `realStandardLie (1 ⊗ₜ Y)`;
  * a linear map `S : K(X) → K(Z)` commuting with `realStandardRep k` for `k ∈ O(n)`, with
    `T ∘ S = id`;
  * a pairwise disjoint list `L` of slots at positions `≥ b`;
  * a weight `W : List ℤ → ℕ` such that `c_J(T u) = W(J) · c_J(u)` on `O(n)` for every
    `J` of length `|L|` and every `u ∈ K(Z)`, with `c_J = coeffs (withModes L J)`.
* `chainData_refl` (identity maps, `L = []`) and `ChainData.mono` (lower the bound `b`).
* `ChainData.step` prepends one block Frobenius step at a position `p` with `p + 1 < b`. It takes
  data `hT : IsBlockFrobData n Z Y p ε σ μ` and `hS : IsBlockFrobData n Y Z p ε σ' μ'`, the recurrence
  for `μ` (so `blockFrobMap hT` is Lie-equivariant, `blockFrobMap_rightDerivative`),
  natural-number values `μ_j = m_j`, and `blockFrobMap hT ∘ blockFrobMap hS = id`. From
  `ChainData n b Y X` it builds `ChainData n p Z X` with `T ∘ blockFrobMap hT`,
  `blockFrobMap hS ∘ S`, the new slot `slotAt p` and the weight `J ↦ m_{j_0} · W(J')`.
  `blockFrobMap hS` is `O(n)`-equivariant (`blockFrobMap_rightTranslation`). The coefficient
  relation combines the Library's `blockFourierCoefficient_blockFrobMap` with
  `blockFourierCoefficient_eq_mul_of_eqOn` and `blockFourierCoefficient_coeffs_eq_mul`; the old slots
  are disjoint from `p, p + 1`.
* Section `Data`: one step at an induction block `d` of weight `ℓ = |d.weight| ≠ 0` placed after the
  list `pre`, followed by `post`. Let `ε = epsW d = (ℓ + 1) mod 2`; then `ℓ - 1 - ε` is even
  (`epsW_par`), and let `p = realRank pre`.
  * `dataT`: `IsBlockFrobData` from `pre ++ [cLow d, cHigh d] ++ post` to
    `pre ++ [induced d] ++ post`, with `σ = 1` and `μ = tailMultiplier ℓ ε 1`. It is built with
    `IsBlockFrobData.of_mid`. The only condition at the induction block, `μ_j = 0` for `|j| < ℓ` in
    the parity class, follows from `tailMultiplier_ne_zero_iff`.
  * `dataS`: the reverse data, with the pointwise inverse multiplier `μ_j⁻¹` (which is `0` where
    `μ_j = 0`).
  * `step_induced`: applies `ChainData.step` to this pair. The recurrence holds with
    `δ = (t - ℓ/2) - (t + ℓ/2) + 1 = 1 - ℓ` (`isRecurrent_tailMultiplier`). For
    `blockFrobMap hT ∘ blockFrobMap hS = id` the Library lemma `blockFrobMap_blockFrobMap_eq` needs
    `Φ^p_j f = 0` on `O(n)` whenever `j ≡ ε (mod 2)` and `μ_j⁻¹ μ_j ≠ 1`. Then `μ_j = 0`, so
    `|j| ≤ ℓ` by `tailMultiplier_ne_zero_iff`, and `|j| < ℓ` by parity (`abs_lt_of_parity`). The
    standard module condition of `f ∈ K(pre ++ [induced d] ++ post)` at the block `d` gives
    `Φ^p_j f = 0` on `O(n)`.
* `chain`: by induction on `rest`, generalizing `pre`, if `realRank (pre ++ rest) = n` then
  `ChainData n (realRank pre) (pre ++ rest.flatMap repl) (pre ++ rest)`. A block kept by `repl` is
  moved into `pre`, using `mono`. An induction block of nonzero weight is handled by
  `step_induced` applied to the chain for `pre ++ [induced d]`. With `pre = []` this gives
  `ChainData n 0 es ds`.

## Section `Form`

From `ChainData n 0 es ds` take `T, S, L, W`.

* `form S` is the sesquilinear form `B(f, h) = ∫_{O(n)} f(k) · conj((S h)(k)) dk`, built with
  `LinearMap.mk₂'ₛₗ`. Integrability holds because the functions are continuous on the compact group
  (`integrable_kf`).
* `form_rep` (**`O(n)`-invariance**): `S(k·h) = k·(S h)`, and the Haar measure is right invariant
  (`integral_mul_right_eq_self`).
* `integral_mul_conj_eq_zero_of_ker`: if `T w = 0` then `∫ f conj w dk = 0` for every `f ∈ K(ds)`.
  By `exists_hasDegree`, `f` has a degree `D` along `L`. By pointwise Parseval each term is
  `c_J(f) conj(c_J(w))`. Since `c_J(f) = c_J(T S f) = W(J) c_J(S f)` and `W(J)` is a real natural
  number, each term equals `c_J(S f) · conj(W(J) c_J(w)) = c_J(S f) · conj(c_J(T w)) = 0`. Then
  `integral_eq_inv_mul_coeffs_zeroModes` gives the claim.
* `eq_zero_of_integral_mul_conj` (**anisotropy**): suppose `∫ f conj(S f) dk = 0`, and let `v = S f`.
  By Parseval and `c_J(f) = W(J) c_J(v)`, the zero-mode coefficient of `f · conj v` at `k ∈ O(n)` is
  `(2π)^{-|L|} Q(k)`, where `Q = Σ_{J ∈ modeLists D |L|} W(J) |c_J(v)|²` is continuous and `≥ 0`.
  So `∫ Q = 0`, hence `Q = 0` on `O(n)`. For each `J`, either `W(J) = 0` or `c_J(v) = 0`, and in
  both cases `c_J(f) = W(J) c_J(v) = 0` on `O(n)`. Parseval for `(f, f)` then gives
  `∫_{O(n)} |f|² = 0`, so `f = 0` on `O(n)`, and `f = 0` by
  `eq_of_eqOn_unitaryCompact_of_mem_principalSeries`.
* `form_lie` (**Lie identity**): for real `X`,
  `B(X f, h) + B(f, X h) = -c_X · B(f, h)` with `c_X = R_X(detPow n (-2r))(1)`.
  Let `w = S(X h) - X(S h)`. Then `T w = X h - X(T S h) = 0`, by Lie-equivariance of `T` and
  `T ∘ S = id`, so `∫ f conj w = 0` by the previous point. Hence
  `B(f, X h) = ∫ f conj(R_X (S h))`. The identity is then `integral_lie_conj` for `f` in the
  principal series of `χ^{ds}` and `S h` in that of `χ^{es}`, with `s = -2r`. Its hypothesis is
  `position_char`, and nonvanishing of `χ^{ds}` is `realPositionCharacter_ne_zero'`.

## The final theorem

`realTemperedForm` takes `r` from the head of `ds` and gets `ChainData n 0 es ds` from `chain ds []`.
It returns `realStandardNontrivial n ds hn` and the form `form S`, with `form_lie` providing the
scalar `-c_X` for each `X`.

## Scope

The form `B` is not shown to be Hermitian. The statement asks only for the stated properties,
which are proved. The scalar in the Lie identity is `-R_X(|det|^{-2r})(1)`. It depends only on
`X` and `r`, which is the real determinant twist that `HasTemperedForm` allows. No formula for it
is proved here.
