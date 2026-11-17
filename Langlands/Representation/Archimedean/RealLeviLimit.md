# The limit argument along a standard parabolic subgroup `Q` of `GL_N(ℝ)`, torus averaged

Lean module: `Langlands.Representation.Archimedean.RealLeviLimit`.

Worker 5220 wrote this module for Task 6749 (`5dd3db87-6f14-4d0f-b9a7-3d0065415fd8`), the proof
of `RealStandardLanglandsQuotientStatement` (module `RealLargeLanglandsQuotientReduction`). It
states and proves `RealLeviLimitStatement` (proof `realLeviLimit`). The statement is the limit
step of the analytic argument for standard modules whose Langlands order has ties. It is
conditional on two of my statements, `RealLeviChartIntegrableStatement` (module
`RealLeviChartIntegralStatement`) and `RealLeviParabolicIntegrationStatement` (module
`RealLeviParabolicIntegrationStatement`). Both are hypotheses of the `Prop`; neither is proved
here.

Provenance: derived. This is internal analytic infrastructure for the proof of
`RealStandardLanglandsQuotientStatement`. No literature statement is claimed. The idea is the
standard one of Langlands-quotient arguments (contract `N̄_Q` by a central element of the Levi
factor and pass to the limit under domination). The precise form, with the average over the
tori of the induction blocks, is specific to this project.

## Notation

`GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ`, `O(N)` is the Library's `unitaryCompact ℝ N`, and
`haarK n` is the Haar probability measure on `O(n)` (Library module
`RealPrincipalSeriesDuality`).

* Real blocks (Library modules `StandardModule`, `RealStrictCharacterLanglandsQuotient`):
  `realRank ds`, `realPositionCharacter ds`, `dualChar χ l x = (χ l x)⁻¹`, `principalSeries`,
  `realStandardModule N ds` and `kFiniteFunctions V (unitaryCompact ℝ N)` (the `O(N)`-finite
  elements of `V`).
* From the module `RealInducedStandardBound`: `realPositionBlockExponent ds p` (the real part of
  the exponent of the block of `ds` containing the position `p`; both positions of an induction
  block get the same value), `slots ds N` (one slot per induction block of `ds`), `absChar e`
  and `expFun N e` (the right `O(N)`-invariant function `b κ ↦ ∏_l |b_ll|^{e_l + (N−1)/2 − l}`
  of the principal series of `absChar e`).
* `coeffs` and `zeroModes` (modules `RealInducedBlockBound`, `RealInducedTorusCore`):
  `c_Z(F) = coeffs (zeroModes (slots ds N)) F 1` is the iterated mode-`0` Fourier coefficient
  over the rotations of the induction blocks of `ds`, evaluated at `1`. By
  `RealLeviTorus.coeffs_eq_integral` it equals `∫ F(τ_θ) dθ`, where
  `τ_θ = torusElem (slots ds N) θ` and `θ` runs over `(0, 2π]^r` with Lebesgue measure.
* The block data of `Q` (module `RealLeviChartIntegralStatement`): `c` blocks of sizes
  `sz : Fin c → ℕ`, `N = ∑ i, sz i`, `cls sz p` the block of `p`, `Coord sz` the coordinates of
  `N̄_Q`, and `lowerGL sz X = n̄(X)`.
* `diag(κ) = blockDiagGL sz κ` for `κ ∈ K_M = ∏_i O(sz_i)`, and `K_M` carries
  `Measure.pi (fun i => haarK (sz i))` (module `RealLeviParabolicIntegrationStatement`).
* `scaleCoord sz s X = X_s`, `scaleGL sz hs = d_s = diag(s^{cls p})`, `blockOrth sz` and
  `adCoord g X = Ad(g) X` (module `RealLeviGeometry`). `G_l = GramFormula.gram l` is the Gram
  determinant of the rows `l, …, N − 1`.

## The statement

`RealLeviLimitStatement` (namespace `Langlands.Archimedean`) says: assume
`RealLeviChartIntegrableStatement` and `RealLeviParabolicIntegrationStatement`. Let `c`, `sz`
and a list of real blocks `ds` with `realRank ds = ∑ i, sz i = N` be given, and write
`t_p = realPositionBlockExponent ds p`. Assume:

* `t_q ≤ t_p` for all positions `p ≤ q` (weak decrease);
* `t_q < t_p` for all positions with `cls sz p < cls sz q` (strict decrease from a block of `Q`
  to a later one).

Let `u` be an `O(N)`-finite element of `principalSeries ℝ N (dualChar (realPositionCharacter ds))`
and `h` an `O(N)`-finite element of `realStandardModule N ds`. If
`∫_{O(N)} u(κ g) h(κ) dκ = 0` for every `g ∈ GL_N(ℝ)`, then

`∫_{K_M} ∫_{Coord sz → ℝ} c_Z(x ↦ u(x · diag(κ)) · h(x · n̄(X) · diag(κ))) dX dκ = 0`,

where `dX` is Lebesgue measure.

Edge cases: if `c ≤ 1`, then `Coord sz` is empty and the `X`-integral is the value at the single
point. If `ds` has no induction blocks, `c_Z(F) = F(1)`.

## Results of the module

All in the namespace `Langlands.Archimedean.RealLeviLimit`.

**Continuity** (section `Cont`): `continuous_lower`, `lower_zero`, `lowerGL_zero`
(`n̄(0) = 1`), `lowerGL_inv_val` (`n̄(X)⁻¹` is the adjugate, since `det n̄(X) = 1`),
`continuous_lowerGL`, `continuous_adCoord_prod` (joint continuity of `(k, X) ↦ Ad(k) X`),
`continuous_scaleCoord`, `continuous_gram`, and `continuous_of_mem_unitaryCompact` (a map into
`O(n)` is continuous into `GL_n(ℝ)` if its matrix is continuous, since the inverse is the
transpose). Also:

* `gramBound γ X = ∏_l G_l(n̄(X))^{γ_l}`, which is continuous (`continuous_gramBound`) and
  nonnegative (`gramBound_nonneg`), and `≤ 1` if all `γ_l ≤ 0` (`gramBound_le_one`). These use
  `1 ≤ G_l(n̄(X))` (`one_le_gram_lower`, module `RealLeviGeometry`).
* `bdK sz κ = diag(κ)`, which lies in `blockOrth sz` (`bdK_mem_blockOrth`) and is continuous in
  `κ` (`continuous_bdK`).
* `continuous_integrand`: `a ↦ F(g(a) · n̄(X(a)) · diag(κ(a)))` is continuous for continuous
  `F`, `g`, `X`, `κ`.

**Limits and bounds** (section `Bounds`).

* `tendsto_scaleCoord`: `X_{n+1} → 0` as `n → ∞`. The coordinate `(p, q)` of `X_s` is
  `s^{−(cls p − cls q)} X_{pq}` with `cls q < cls p`.
* `tendsto_lowerGL_scale`: `n̄(X_{n+1}) k → k`.
* `exists_bound_mul_tendsto`: a continuous `F` is bounded on `O(N) · {g_n}` for a convergent
  sequence `g_n` (compactness of `O(N) × ({g_0} ∪ {g_n})`).
* `norm_le_gram_lower`: the growth bound `RealLeviTorus.norm_le_gram_fin` at `y = n̄(Y)`
  (`G_0(n̄(Y)) = 1` because `det n̄(Y) = 1`): `‖F(n̄(Y) κ)‖ ≤ C · gramBound ε Y`.
* `isSignedPower_absChar`: `absChar e` is a signed power with exponents `e`.
* `norm_expFun_le`: `‖expFun N e (n̄(Y) κ)‖ ≤ gramBound ε Y` for `κ ∈ O(N)` and
  `ε_l = (e_l − e_{l−1} − 1)/2` (`l ≥ 1`). Here `σ_l = e_l + (N − 1)/2 − l`, and
  `expFun N e = 1` on `O(N)`.
* the existing `JacquetLimit.norm_modulusCharacter` and `norm_modulusCovariant_le`: a modulus covariant function bounded by
  `C` on `O(N)` satisfies `‖F(n̄(Y) κ)‖ ≤ C · gramBound (fun _ => −1) Y`, since the modulus
  character has `σ_l = (N − 1) − 2l`.
* `gammaExp t l`: `−1` for `l = 0`, and `max((t_{l−1} − t_l − 1)/2, 0) + (t_l − t_{l−1} − 1)/2`
  for `l ≥ 1`. If `t_l ≤ t_{l−1}`, then `gammaExp t l ≤ −1/2` (`gammaExp_le`); if
  `t_l < t_{l−1}`, it is `< −1/2` (`gammaExp_lt`). `gammaExp_nonpos` collects the signs.
* `gramBound_mul_le` (**domination**): for `s ≥ 1`,
  `gramBound ε^u (Y_s) · gramBound ε^h Y ≤ gramBound (gammaExp t) Y`, with
  `ε^u_l = (t_{l−1} − t_l − 1)/2` and `ε^h_l = (t_l − t_{l−1} − 1)/2`.

**Exchange of integrals** (section `Fubini`).

* `integrable_comp_adCoord`: if `B` is continuous and integrable on `Coord sz → ℝ`, `μ` is a
  finite measure and `T` is continuous with values in `blockOrth sz`, then
  `(X, θ) ↦ B(Ad(T θ) X)` is integrable on `volume × μ`.
* `integral_swap_torus`: for `f(κ, X, θ)` jointly continuous, finite measures `μ_K` and `μ`, and
  a bound `‖f(κ, X, θ)‖ ≤ b(X, θ)` with `b` integrable on `volume × μ` and every `b(·, θ)`
  integrable,
  `∫_κ ∫_X ∫_θ f = ∫_θ ∫_κ ∫_X f`.

**Fixed scale** (section `FixedScale`). `integral_torus_scale_eq_zero`: assume the two
statements, let `χ` be a signed power, `u ∈ principalSeries ℝ N (dualChar χ)`,
`h ∈ principalSeries ℝ N χ` with `∫_{O(N)} u(κ g) h(κ) dκ = 0` for all `g`, and let `L` be a list
of slots, each inside one block of `Q` (`cls sz s.p = cls sz (s.p + 1)`). Then for every `s > 0`,

`∫_{K_M} ∫_X ∫_θ u(τ_θ n̄(X_s) diag(κ)) · h(τ_θ n̄(X) diag(κ)) dθ dX dκ = 0`,

with `τ_θ = torusElem L θ` and `θ` distributed by `torusMeasure L.length`.

**The limit** (section `Limit`).

* `slots_cls_eq`: under strict decrease across the blocks of `Q`, every slot of `slots ds N` lies
  inside one block of `Q`. The two positions of an induction block have the same value of
  `realPositionBlockExponent` (`induced_at`, module `RealInducedStandardBound`), so they cannot
  lie in different blocks.
* `integral_coeffs_eq_zero`: the conclusion of `RealLeviLimitStatement`.

## Proof

**Fixed scale.** Let `d = d_s` and `G(y) = u(y d) h(y)`. The right translate of `u` by `d` is
still in the principal series of `dualChar χ` (`rightTranslation_mem_principalSeries`). So `G` is
smooth (`contMDiff_mul_fun`) and modulus covariant: the characters of `u` and `h` multiply to the
modulus character (`principalSeriesCharacter_dual_mul`). By
`RealLeviParabolicIntegrationStatement`, `∫_{O(N)} G = C ∫_{K_M} ∫_X G(n̄(X) diag(κ))` with
`C > 0`. The left side is `∫_{O(N)} u(κ d) h(κ) dκ = 0` by hypothesis at `g = d`. So
`∫_{K_M} ∫_X G(n̄(X) diag(κ)) = 0`. For fixed `θ`, `τ = τ_θ ∈ blockOrth sz`
(`torusElem_mem_blockOrth`), and `τ n̄(X) = n̄(Ad(τ) X) τ` (`mul_lowerGL`). The substitution
`X ↦ Ad(τ) X` (`integral_adCoord`) and the left invariance `integral_blockOrth_mul` give
`∫_{K_M} ∫_X G(τ n̄(X) diag(κ)) = ∫_{K_M} ∫_X G(n̄(X) diag(κ)) = 0` for every `θ`.

Next, `τ n̄(X) diag(κ) d = d τ n̄(X_s) diag(κ)`, because `d` commutes with block orthogonal
elements (`mul_scaleGL`) and `n̄(X) d = d n̄(X_s)` (`lowerGL_mul_scaleGL`). With
`u(d y) = c' u(y)` (`c'` the value of the character of `u` at the diagonal of `d`, which is
nonzero), the integrand is `c'⁻¹ · G(τ n̄(X) diag(κ))`. It remains to exchange `∫_θ` with
`∫_κ ∫_X` (`integral_swap_torus`). Let `C_G` bound `|G|` on `O(N)`
(`exists_bound_unitaryCompact`). Then
`|G(τ n̄(X) diag(κ))| = |G(n̄(Ad(τ) X) τ diag(κ))| ≤ C_G · gramBound (fun _ => −1) (Ad(τ) X)`
(`norm_modulusCovariant_le`). The function `gramBound (fun _ => −1)` is integrable by
`RealLeviChartIntegrableStatement` with `γ = −1` (both conditions hold since `−1 < −1/2`). So the
bound is integrable on the product (`integrable_comp_adCoord`) and for each `θ`
(`measurePreserving_adCoord`).

**The limit.** Let `L = slots ds N`. Its slots lie inside the blocks of `Q` (`slots_cls_eq`). Let
`τ_θ = torusElem L θ`, `s_n = n + 1`, and

`Ψ_n(κ, X) = ∫_θ u(τ_θ n̄(X_{s_n}) diag(κ)) h(τ_θ n̄(X) diag(κ)) dθ`,
`Ψ(κ, X) = ∫_θ u(τ_θ diag(κ)) h(τ_θ n̄(X) diag(κ)) dθ`.

By the fixed-scale identity (with `χ = realPositionCharacter ds`, a signed power by
`isSignedPower ds`), `∫_{K_M} ∫_X Ψ_n = 0` for every `n`. By `coeffs_eq_integral`,
`Ψ(κ, X) = c_Z(x ↦ u(x diag(κ)) h(x n̄(X) diag(κ)))`. So it suffices to show
`∫_{K_M} ∫_X Ψ_n → ∫_{K_M} ∫_X Ψ`. This uses dominated convergence three times.

* **Domination in `X`.** Write `y_1 = n̄(X_{s_n}) diag(κ)` and `y_2 = n̄(X) diag(κ)`. By
  `coeffs_eq_integral`, `Ψ_n(κ, X)` is the torus coefficient of `x ↦ u(x y_1) h(x y_2)`. The
  torus-pairing bound `RealInducedStandardBound.exists_bound` gives a constant `C_0` with
  `|Ψ_n(κ, X)| ≤ C_0 |∫_θ E_u(τ_θ y_1) E_h(τ_θ y_2) dθ|`, where `E_u = expFun N (−t)` and
  `E_h = expFun N t`. Now `τ_θ y_1 = n̄((Ad(τ_θ) X)_{s_n}) τ_θ diag(κ)` (using
  `adCoord_scaleCoord`) and `τ_θ y_2 = n̄(Ad(τ_θ) X) τ_θ diag(κ)`, with `τ_θ diag(κ) ∈ O(N)`.
  `norm_expFun_le` with `e = −t` and `e = t` gives the exponents `ε^u` and `ε^h`, and
  `gramBound_mul_le` (`s_n ≥ 1`) gives
  `|E_u(τ_θ y_1) E_h(τ_θ y_2)| ≤ gramBound γ (Ad(τ_θ) X)` with `γ_l = gammaExp t l`. Hence
  `|Ψ_n(κ, X)| ≤ D(X) = max(C_0, 0) · ∫_θ gramBound γ (Ad(τ_θ) X) dθ`, uniformly in `n` and `κ`.
* **Integrability of `D`.** Weak decrease gives `γ_l ≤ −1/2` for `l ≥ 1` (`gammaExp_le`). Strict
  decrease across blocks gives `γ_l < −1/2` when `l − 1` and `l` lie in different blocks
  (`gammaExp_lt`). So `gramBound γ` is integrable by `RealLeviChartIntegrableStatement`. By
  `integrable_comp_adCoord` and Fubini (`Integrable.integral_prod_left`), `D` is integrable. For
  fixed `X`, the `θ`-integrand is bounded by `1` (`gramBound_le_one`) on a finite measure.
* **Innermost limit (`θ`).** For fixed `κ, X`, `n̄(X_{s_n}) diag(κ) → diag(κ)`
  (`tendsto_lowerGL_scale`), so the integrand converges pointwise by continuity of `u`. It is
  bounded by the constant `M_u M_h`, from `exists_bound_mul_tendsto` and
  `RealLeviTorus.exists_bound_mul`, since `τ_θ ∈ O(N)`. So `Ψ_n(κ, X) → Ψ(κ, X)`.
* **Middle limit (`X`).** Dominated convergence with the integrable bound `D`. Measurability of
  `X ↦ Ψ_n(κ, X)` comes from the joint continuity of the integrand
  (`AEStronglyMeasurable.integral_prod_right'`).
* **Outer limit (`κ`).** Dominated convergence on the finite measure on `K_M` with the constant
  bound `∫ D`.

Since `∫_{K_M} ∫_X Ψ_n = 0` for all `n`, the limit `∫_{K_M} ∫_X Ψ` is `0`
(`tendsto_nhds_unique`).

`realLeviLimit` applies `integral_coeffs_eq_zero`.

## Use

In the proof of `RealStandardLanglandsQuotientStatement` for lists with ties, the hypothesis
`∫_{O(N)} u(κ g) h(κ) dκ = 0` for all `g` says that the matrix coefficients of `h` against the
dual principal series vanish. This module turns that into the vanishing of a pairing over the
Levi data `K_M × N̄_Q`, averaged over the tori of the induction blocks. The planned next steps of
the proof (not part of this module) use it to show that such an `h` is zero.
