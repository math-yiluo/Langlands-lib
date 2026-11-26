# Descent of vanishing ordinary integrals along the last row

Module `Langlands.Global.RankinSelberg.RealUnequalLastRowDescent`. Helper declarations are in the
namespace `Langlands.Global.RankinSelbergGlobal.RealUnequalLastRowDescent`; the statement and its
proof are in `Langlands.Global.RankinSelbergGlobal`.

Notation: `G_m = GL_m(ℝ)`, `Q_n = N_(n+1) \ G_(n+1)` (`LeftUnipotentQuotient n ℝ`), `e(x) = exp(2πix)`
(`Real.fourierChar`), `diag(g, 1) = padGL _ g`. For `t < r`, `realUnequalIntegral h D W V s` is the
ordinary integral `∫_(Q_t) W(diag(g, 1)) V(g) |det g|^(s - (r-t)/2) dD(g)` of the Library
(module `ArchimedeanIntegrals`).

## Statement

`RealUnequalLastRowDescentStatement`: let `n + 1 < r`, `D` and `D'` compatible real quotient measure
data on `Q_n` and `Q_(n+1)`, `a ∈ ℝˣ`, and let `W` on `G_(r+1)` and `V` on `G_(n+2)` be continuous,
with left characters `a` and `-a` under the upper unipotent groups (`HasLeftCharacter`), and with the
simple-root gauge bounds `HasGaugeBound` of module `RealWhittakerTranslatedMellin`. Suppose that for
every `y ∈ ℝ^(n+2)` the ordinary integral of `x ↦ W(x · colUnip y)` against `V` vanishes on some right
half-plane, where `colUnip y = 1 + Σ_(i ≤ n+1) y_i E_(i, n+2)` is the upper column unipotent element in
the column just right of the `G_(n+2)` block. Then the ordinary integral of `W` against the restriction
`z ↦ V(diag(z, 1))` (for `D`) vanishes on some right half-plane.

`realUnequalLastRowDescent` proves it (from `lastRow_descent`). The proofs use only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`.

## Proof

**Fourier uniqueness** (`eq_zero_of_fourier_eq_zero`, `eq_zero_of_fourier_units_eq_zero`). Let
`Ψ ∈ L¹(ℝ^(n+1) × ℝ)` have all Fourier coefficients `∫ e(⟨x, y⟩ + u c) Ψ(x, u) dx du` equal to zero
and be continuous at `(0, 1)`. Transport `Ψ` to `EuclideanSpace ℝ (Fin (n+2))` by the measure-preserving
splitting `splitLast` into the first `n + 1` coordinates and the last one; there its Fourier transform
`𝓕` vanishes, and Mathlib's inversion theorem `Integrable.fourierInv_fourier_eq` at the point
`splitLast⁻¹ (0, 1)` gives `Ψ(0, 1) = 0`. For `G` on `ℝ^(n+1) × ℝˣ`, integrable for `dx |u|⁻¹ du`
(`volume.prod RealRankZero.unitsHaar`), the same holds for `Ψ(x, u) = |u|⁻¹ unitsExtend2 G (x, u)`,
where `unitsExtend2` extends by zero at `u = 0`: `map_prodVal`, `integrable_units_iff` and
`integral_units_eq` identify `dx |u|⁻¹ du` with `|u|⁻¹ dx du` under `(x, u) ↦ (x, u)`.

**The column phase** (`colUnip`, `padGL_mul_colUnip`, `character_colUnip`, `integrand_colUnip`).
For `g ∈ G_(k+1)`, `diag(g, 1) colUnip y = colUnip (g y) diag(g, 1)`, and the Whittaker character of
`colUnip z` is `e(a z_k)`. Hence the ordinary integrand of `x ↦ W(x colUnip y)` against `V` is
`e(a ⟨ξ(q), y⟩)` times that of `W` against `V`, where `ξ(q)` is the last row of a representative
(`lastRowQ`, well defined by `lastRow_unipotent_mul`).

**The integrand at chart points** (`lowerBlockPair_eq`, `logDet_lastRowFactor`,
`integrand_lastRowChart`, `fibre_eq`). With `L(x, u) = [[1, 0], [x, u]] ∈ G_(n+2)`
(`lastRowFactor`), the chart point `[[g, 0], [x, u]]` of the module `RealLowerBlockChart` is
`diag(g, 1) L(x, u)`. The ordinary integrand of `(W, V)` at `s` there, times `|det g|⁻¹`, is
`|u|^(s - (r-n-1)/2)` times the ordinary integrand at `[g]` and `s - 1/2` of the translates
`W_L = (z ↦ W(z diag(L, 1)))` and `V_L = (z ↦ V(diag(z, 1) L))`; the shift uses
`(r - n)/2 = (r - n - 1)/2 + 1/2`. Integrating over `Q_n` against `|det g|⁻¹ dD`
(`integral_withDensity_eq_integral_smul`):
`G(x, u) := ∫ Φ_s([[g,0],[x,u]]) |det g|⁻¹ dD([g]) = |u|^(s - (r-n-1)/2) Ψ(s - 1/2; W_L, V_L)`.

**Continuity** (`continuousAt_translateIntegral`). For a compact neighbourhood `K` of `1` in `G_(n+2)`,
the families `W_L` and `V_L`, `L ∈ K`, have uniform gauges: `compact_rightTranslate_uniformGauge` of
the Library for right translates (`hasUniformGauge_translate`), followed for `V_L` by the Library's
`HasUniformGauge.pad` (`hasUniformGauge_pad_translate`). The Library's
`ordinary_halfPlaneDomination` then gives integrable majorants on a right half-plane, uniform in
`L ∈ K`, and dominated convergence (`continuousAt_of_dominated`) gives continuity of
`L ↦ Ψ(s'; W_L, V_L)` at `1`. Together with continuity of `lastRowFactor`
(`continuous_lastRowFactor`, `lastRowFactor_zero_one`), `G` is continuous at `(0, 1)`.

**Descent** (`lastRow_descent`). `ordinary_halfPlaneDomination` for `(W, V)` gives a half-plane
`Re s > σ₀` of integrable domination; the translates have integrands of the same absolute value, so
their integrals are holomorphic there (`differentiableOn_of_dominated`) and, vanishing on some
smaller half-plane, vanish on `Re s > σ₀` by the identity theorem (`eq_zero_on_right`). Fix `s` with
`Re s > σ₀` and `Re(s - 1/2)` above the continuity threshold. For `y ∈ ℝ^(n+2)`,
`∫ e(a ⟨ξ(q), y⟩) Φ_s(q) dD'(q) = 0`. By `lastRowChart_integral` (with `C > 0`) and Fubini
(`integral_prod_symm`, `Integrable.integral_prod_right`), using `lastRowQ_chart`
(`⟨ξ([[g,0],[x,u]]), y⟩ = ⟨x, y'⟩ + u y_last`), every Fourier coefficient of `G` vanishes; choosing
`y = (y''/a, c/a)` reaches every frequency. Fourier uniqueness gives `G(0, 1) = 0`, and `G(0, 1)` is the
ordinary integral of `W` against `V ∘ diag(·, 1)` at `s - 1/2`.

`hasGaugeBound_pad` (restriction along `diag(·, 1)` preserves `HasGaugeBound`, from the Iwasawa
decomposition and the Library's `rootPos_padVec`, `sum_abs_padVec`) and `hasLeftCharacter_pad`
(restriction preserves the left character, from `realWhittakerCharacter_padGL`) are recorded for
iterating the descent. `ArchimedeanRealPairIdentity.sigmaCompactSpace_quotient` and `ArchimedeanRealPairIdentity.sigmaFinite_measure` give σ-finiteness of
compatible quotient measures.

## Provenance

Internal. This is the last-row argument of H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
§6.2, Propositions 6.1–6.2, pp. 41–42 of the author-posted version. There, right translates of a
Whittaker function by upper column unipotent elements multiply its restriction to `diag(g, 1)` by a
character of the last row of `g`. Averaging these translates against the Fourier transform of a
Schwartz function `Φ` on the row space multiplies the restriction by `Φ` evaluated at the last row
(Proposition 6.1). For a smooth compactly supported function `φ(x, h)` on `F^t × F^×`, extended by
zero to a Schwartz function on `F^(t+1)`, this multiplies the restriction to `[[g, 0], [x, h]]` by
`φ(x, h)` (Proposition 6.2). The Lean proof does not average: it uses the individual column phases and
runs the argument in the dual direction. Vanishing for all characters of the last row is turned, by
Fourier inversion in the coordinates `(x, h)` and continuity at `(0, 1)`, into vanishing of the
integral over the smaller group. The measure decomposition is `RealLastRowChartStatement` (module
`RealLowerBlockChart`).
