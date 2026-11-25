# The limit along a standard parabolic subgroup `Q` of `GL_N(ℝ)`: value form

Module `Langlands.Representation.Archimedean.RealParabolicLimitValue`, namespace
`Langlands.Archimedean.RealParabolicLimitValue`.

## Purpose and provenance

Module `RealLeviLimit` proves the vanishing form of the limit along a
standard parabolic subgroup `Q`: the torus-averaged limit pairing `Θ(u, h)` (defined below) is `0`
when all matrix coefficients `∫_{O(N)} u(κ g) h(κ) dκ` vanish. This module proves the **value
form**: two pairs `(u, h)` and `(u', h')` whose matrix coefficients agree at every central
scaling `d_s` of `Q` have the same limit pairing, `Θ(u, h) = Θ(u', h')`.

This is internal infrastructure for the reverse-intertwiner step of the proof of
`RealStandardIrreducibleCriterionStatement` (`RealReverseIntertwinerKernelStatement`, module
`RealStandardIrreducibleCriterionReduction`) for
lists with induction blocks: there the matrix coefficients of two different pairs are shown to
agree on the diagonal elements `d_s`, and the value form transfers this to their limit pairings.

Provenance: derived. No literature statement is claimed. The statements and proofs are those of
`RealLeviLimit.integral_torus_scale_eq_zero` and `RealLeviLimit.integral_coeffs_eq_zero`, with
"`= 0`" replaced by an explicit formula at each scale. The dominated-convergence argument of
`tendsto_integral_scale` is copied from the proof of `RealLeviLimit.integral_coeffs_eq_zero`.

Like `RealLeviLimitStatement`, the results are conditional on the two statements
`RealLeviChartIntegrableStatement` (module `RealLeviChartIntegralStatement`) and
`RealLeviParabolicIntegrationStatement` (module `RealLeviParabolicIntegrationStatement`). Both
appear as hypotheses `hT1`, `hT3`; neither is proved here.

## Notation

As in `RealLeviLimit.md`. `GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ`, `O(N)` is
`unitaryCompact ℝ N` with Haar probability measure `haarK N`. `Q` has `c` diagonal blocks of
sizes `sz : Fin c → ℕ`, `N = ∑ i, sz i`; `cls sz p` is the block of the position `p`;
`Coord sz` are the coordinates of `N̄_Q`, `n̄(X) = lowerGL sz X`; `K_M = ∏_i O(sz_i)` with
measure `Measure.pi (fun i => haarK (sz i))` and `diag(κ) = bdK sz κ`;
`d_s = scaleGL sz hs = diag(s^{cls p})` for `s > 0` (`hs : 0 < s`) and `X_s = scaleCoord sz s X`.
For a list `L` of slots, `τ_θ = torusElem L θ` with `θ` distributed by
`torusMeasure L.length`. For a list `ds` of real blocks, `c_Z(F) =
coeffs (zeroModes (slots ds N)) F 1` (the iterated mode-`0` Fourier coefficient over the
rotations of the induction blocks), and

`Θ(u, h) = ∫_{K_M} ∫_{Coord sz → ℝ} c_Z(x ↦ u(x diag(κ)) · h(x n̄(X) diag(κ))) dX dκ`.

## Statements

All in the namespace `Langlands.Archimedean.RealParabolicLimitValue`.

- `integral_torus_eq hT1 hC hT3 hGs hG L hL`: let `C > 0` and assume the integration formula
  `∫_{O(N)} F = C · ∫_{K_M} ∫_X F(n̄(X) diag(κ))` (with integrability of the inner integrands)
  for every smooth modulus covariant `F` (`hT3`, the conclusion of
  `RealLeviParabolicIntegrationStatement` for the fixed `sz`). Let `G` be smooth (`hGs`) and
  modulus covariant (`hG`), and `L` a list of slots each inside one block of `Q`
  (`cls sz s.p = cls sz (s.p + 1)`, `hL`). Then

  `∫_{K_M} ∫_X ∫_θ G(τ_θ n̄(X) diag(κ)) dθ dX dκ = μ(univ) · (C⁻¹ · ∫_{O(N)} G(κ) dκ)`,

  with `μ = torusMeasure L.length` (`μ(univ)` its total mass as a real number).
- `exists_integral_torus_scale_eq hT1 hT3 c sz`: there is `C > 0` such that for every signed
  power `χ` with exponents `e`, every `u ∈ principalSeries ℝ N (dualChar χ)`,
  `h ∈ principalSeries ℝ N χ`, every list `L` of slots each inside one block of `Q`, and every
  `s > 0`,

  `∫_{K_M} ∫_X ∫_θ u(τ_θ n̄(X_s) diag(κ)) · h(τ_θ n̄(X) diag(κ)) dθ dX dκ
   = c'(s)⁻¹ · (μ(univ) · (C⁻¹ · ∫_{O(N)} u(κ d_s) h(κ) dκ))`,

  where `c'(s)` is `principalSeriesCharacter ℝ N (dualChar χ)` evaluated at the diagonal of
  `d_s` (the vector `p ↦ s^{cls p}`, `scaleVec sz s`).
- `tendsto_integral_scale hT1 hN hanti hstrict hu hh`: let `ds` be a list of real blocks with
  `realRank ds = N` (`hN`), write `t_p = realPositionBlockExponent ds p`, and assume `t_q ≤ t_p`
  for `p ≤ q` (`hanti`) and `t_q < t_p` when `cls sz p < cls sz q` (`hstrict`) — the hypotheses
  of `RealLeviLimitStatement`. Let `u` be an `O(N)`-finite element of
  `principalSeries ℝ N (dualChar (realPositionCharacter ds))` and `h` an `O(N)`-finite element
  of `realStandardModule N ds`. Then, with `L = slots ds N`,

  `∫_{K_M} ∫_X ∫_θ u(τ_θ n̄(X_{n+1}) diag(κ)) · h(τ_θ n̄(X) diag(κ)) dθ dX dκ → Θ(u, h)`

  as `n → ∞` (`n : ℕ`).
- `integral_coeffs_eq_of_eq hT1 hT3 hN hanti hstrict hu hh hu' hh' h0` (**value form**): with
  `ds`, `hN`, `hanti`, `hstrict` as above, let `u, u'` be `O(N)`-finite elements of
  `principalSeries ℝ N (dualChar (realPositionCharacter ds))` and `h, h'` `O(N)`-finite elements
  of `realStandardModule N ds`. If for every `s > 0`

  `∫_{O(N)} u(κ d_s) h(κ) dκ = ∫_{O(N)} u'(κ d_s) h'(κ) dκ`   (`h0`),

  then `Θ(u, h) = Θ(u', h')`.

Edge cases are those of `RealLeviLimit`: if `c ≤ 1` then `Coord sz` is empty and the
`X`-integral is evaluation at the single point; if `ds` has no induction blocks, `L` is empty,
the torus measure is a point mass and `c_Z(F) = F(1)`.

## Proofs

`integral_torus_eq`. Fix `θ`; `τ = τ_θ` lies in `blockOrth sz` (`torusElem_mem_blockOrth`,
using `hL`). Since `τ n̄(X) = n̄(Ad(τ) X) τ` (`mul_lowerGL`), the substitution `X ↦ Ad(τ) X`
(`integral_adCoord`) and the left invariance of the `K_M`-integral under block orthogonal
elements (`integral_blockOrth_mul`) give

`∫_{K_M} ∫_X G(τ n̄(X) diag(κ)) = ∫_{K_M} ∫_X G(n̄(X) diag(κ)) = C⁻¹ ∫_{O(N)} G`,

the last step by the integration formula `hT3` (and `C ≠ 0`). The `θ`-integral is exchanged with
the `κ`- and `X`-integrals by `RealLeviLimit.integral_swap_torus`, with the integrable bound
`C_G · gramBound (fun _ => −1) (Ad(τ_θ) X)`: here `C_G` bounds `|G|` on `O(N)`
(`exists_bound_unitaryCompact`), the pointwise estimate is `norm_modulusCovariant_le`, and the
bound is integrable by `RealLeviChartIntegrableStatement` at `γ = −1`, by
`integrable_comp_adCoord` on the product and by `measurePreserving_adCoord` for fixed `θ`. The
`θ`-integral of the constant `C⁻¹ ∫_{O(N)} G` is `μ(univ)` times it (`integral_const`).

`exists_integral_torus_scale_eq`. Take `C` from `RealLeviParabolicIntegrationStatement` for
`sz`. Let `d = d_s` and `G(y) = u(y d) h(y)`. As in
`RealLeviLimit.integral_torus_scale_eq_zero`, `G` is smooth and modulus covariant (the right
translate of `u` by `d` stays in the principal series; the characters of `u` and `h` multiply to
the modulus character, `principalSeriesCharacter_dual_mul`). The identity
`τ_θ n̄(X) diag(κ) d = d · τ_θ n̄(X_s) diag(κ)` (`mul_scaleGL`, `lowerGL_mul_scaleGL`) and
`u(d y) = c'(s) u(y)` (left covariance of `u` at the diagonal element `d`) give
`u(τ_θ n̄(X_s) diag(κ)) h(τ_θ n̄(X) diag(κ)) = c'(s)⁻¹ G(τ_θ n̄(X) diag(κ))`; `c'(s) ≠ 0` since
its norm is a product of positive powers (`norm_principalSeriesCharacter`). Pull out the
constant (`integral_const_mul`) and apply `integral_torus_eq`; finally
`∫_{O(N)} G = ∫_{O(N)} u(κ d_s) h(κ) dκ`.

`tendsto_integral_scale`. This is the dominated-convergence part of the proof of
`RealLeviLimit.integral_coeffs_eq_zero`, stated as a convergence result; see the section "The
limit" of `RealLeviLimit.md`. The slots of `L = slots ds N` lie inside the blocks of `Q`
(`slots_cls_eq`). With `Ψ_n(κ, X) = ∫_θ u(τ_θ n̄(X_{n+1}) diag(κ)) h(τ_θ n̄(X) diag(κ)) dθ`:

- domination `|Ψ_n(κ, X)| ≤ D(X) = max(C_0, 0) · ∫_θ gramBound γ (Ad(τ_θ) X) dθ`, uniformly in
  `n` and `κ`, from the torus-pairing bound `RealInducedStandardBound.exists_bound`, the bounds
  `norm_expFun_le` and the domination `gramBound_mul_le`, with `γ_l = gammaExp t l`;
- `D` is integrable: `gramBound γ` is integrable by `RealLeviChartIntegrableStatement`
  (`gammaExp_le` from `hanti`, `gammaExp_lt` from `hstrict`), then `integrable_comp_adCoord`
  and Fubini;
- three applications of dominated convergence (in `θ` with a constant bound from
  `exists_bound_mul_tendsto` and `exists_bound_mul`; in `X` with `D`; in `κ` with the constant
  `∫ D`), using `n̄(X_{n+1}) diag(κ) → diag(κ)` (`tendsto_lowerGL_scale`);
- the limit `∫_θ u(τ_θ diag(κ)) h(τ_θ n̄(X) diag(κ)) dθ` equals
  `c_Z(x ↦ u(x diag(κ)) h(x n̄(X) diag(κ)))` by `coeffs_eq_integral`.

`integral_coeffs_eq_of_eq`. Take `C` from `exists_integral_torus_scale_eq`, and `L = slots ds N`
(slots inside the blocks of `Q` by `slots_cls_eq`). The character `realPositionCharacter ds` is a
signed power (`isSignedPower ds`). For every `n`, apply `exists_integral_torus_scale_eq` at
`s = n + 1` to both pairs: the two approximating integrals are
`c'(s)⁻¹ · (μ(univ) · (C⁻¹ · m))` with the same `c'(s)`, `μ` and `C`, and with the matrix
coefficients `m` at `d_s` of the two pairs, which are equal by `h0`. So the two sequences of
approximating integrals coincide. By `tendsto_integral_scale` they converge to `Θ(u, h)` and to
`Θ(u', h')`, so the limits agree (`tendsto_nhds_unique`).
