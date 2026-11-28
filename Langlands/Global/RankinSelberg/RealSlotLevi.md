# The inner Levi integral along the slot open cells

Lean module: `Langlands.Global.RankinSelberg.RealSlotLevi`.

This is a helper module of the proof of
`Langlands.Global.RankinSelbergGlobal.RealTemperedWhittaker.RealTemperedWhittakerBoundStatement`
(see `RealTemperedWhittakerBoundProof.md`). It states no `Prop`-valued statement; it proves lemmas
only. The content is internal and follows no literature source. Unprefixed names are in the
namespace `Langlands.Global.RankinSelbergGlobal.RealLeviStages`. `standardSection z φ` is the
standard section of the compact profile `φ` with exponents `z` (module
`RealGodementCompactProfile`); the slot matrices and the core bound are those of
`RealSlotMatrices` and `RealSlotCore`.

## Slot coordinates

`SlotSet.ext S x` extends coordinates `x : S.starts → ℝ` by zero to all natural numbers
(`ext_coe`). `diag_congr`, `rot_congr`, `slotVec_congr` and `cellExponent_congr` show that the slot
matrices and vectors only depend on their values at the starts. `sum_mul_slotVec` and
`sum_mul_slotVec_real` write a pairing with `slotVec S u v` as a sum over the slots.

## Exponential equivariance of standard sections

- `shiftExp z i = z_i + (N - 1)/2 - i` are the shifted exponents of a standard section.
- `standardSection_unipotent_torus_mul`: for `v` upper unipotent,
  `standardSection z φ (v · torus γ · g) = exp(Σ_i shiftExp z i · γ_i) · standardSection z φ g`
  (`RealBlockDerivative.isExpEquivariant_of_mem_principalSeries`).
- `continuous_standardSection`, `isKFin_standardSection`, `norm_standardSection_unitary_le` (a bound on
  `O(N)`), and `standardSection_eq_on_unitary` (the values on `O(N)` do not depend on `z`).

## The inner Levi integral

- `leviIntegral S F b g = ∫ F(swapGL S · unip S (ext x) · g) e^{2πi Σ_q b_q x_q} dx` over the slot
  coordinates `x : S.starts → ℝ`: the Jacquet integral of the Levi subgroup with the two-by-two
  blocks on the slots, with the phases `b_q`.
- `slotScale α p = exp(α_{p+1} - α_p)`.
- `leviIntegral_standardSection`: if `z_{first q} - z_{second q} = m_q` on every slot, then by
  `swapGL_unip_mul` the inner integral of a standard section at `g` is
  `exp(Σ_i shiftExp z i · α_{perm i}(g))` times the integral of the core integrand of `RealSlotCore`
  at the orthogonal point `swapGL S · kpart g`, with the affine coordinates
  `c = slotCoord (npart g)` and `s = slotScale (alpha g)`. The factor `ρ^{-(m_q + 1)}` comes from the
  cell exponents (`exp_neg_log_cellNorm`).
- `norm_leviIntegral_le`: let `φ` be a compact profile (`IsCompactProfile p φ`), let the weights
  `m_q` be nonzero on every slot, and let the standard section of `φ` at one exponent `z₀` have
  `SlotModes` along the slots with the weights `m`. Then there is `C ≥ 0` such that for every `z`
  with `z_{first q} - z_{second q} = m_q` on every slot, every `b` and every `g`,
  `‖leviIntegral S (standardSection z φ) b g‖ ≤ C exp(Σ_i Re shiftExp z i · α_{perm i}(g)) ·
  ∏_q s_q⁻¹ |b_q / s_q|^{m_q/2}`. The constant is `coreConstant` (`core_bound`); it does not
  depend on `z`, because the values on `O(N)` do not.

## The spherical form of the bound

- `rhoShift i = (N - 1)/2 - i`, and `blockRe S m z i = Re z_i - slotVec(m/2, -m/2)_i`: the real
  parts of the exponents minus the signed slot half-weights (`m_q/2` subtracted at the first
  position of the slot `q`, added at the second). When `Re z_{first q} - Re z_{second q} = m_q`,
  both values on the slot equal the average of the two real parts.
- `shiftExp_perm_re` and `levi_exponent_identity`: the permuted shifted exponents together with the
  scale factors `(1 + m_q/2)(α_{first q} - α_{second q})` give `Σ_i (blockRe S m z i + rhoShift i) α_i`.
- `slotScale_factor`: for `p + 1 < N`, `s_p⁻¹ |b / s_p|^{m/2}` with `s_p = slotScale α p` equals
  `|b|^{m/2} exp((1 + m/2)(α_p - α_{p+1}))`.
- `norm_leviIntegral_le_spherical`: under the hypotheses of `norm_leviIntegral_le`,
  `‖leviIntegral S (standardSection z φ) b g‖ ≤ C (∏_q |b_q|^{m_q/2}) exp(Σ_i (blockRe S m z i +
  rhoShift i) α_i(g))`. This is the scalar Fourier bound in each two-by-two block times the
  spherical function of the block-averaged exponents.
