# The Levi-staged Jacquet family along the block deformation

Lean module: `Langlands.Global.RankinSelberg.RealSlotStagedFamily`.

This is a helper module of the proof of
`Langlands.Global.RankinSelbergGlobal.RealTemperedWhittaker.RealTemperedWhittakerBoundStatement`
(see `RealTemperedWhittakerBoundProof.md`). It states no `Prop`-valued statement; it proves lemmas
only. The content is internal and follows no literature source. Unprefixed names are in the
namespace `Langlands.Global.RankinSelbergGlobal.RealLeviStages`. `canonicalJacquetFamily a hφ z` is
the holomorphic continuation in `z` of the Jacquet integral of the standard section of the profile
`φ` (module `RealGodementCanonicalCoefficient`), and `Langlands.Analysis.dominatedHolomorphicIntegral`
the holomorphy of locally dominated integrals of holomorphic functions.

The standing hypotheses (those of `norm_leviIntegral_deform_le`, `norm_stagedIntegrand_le`,
`stagedIntegral_holomorphic`, `canonical_eq_stagedFamily` and `norm_canonical_deform_le`) are: a
slot set `S`, weights `m_q ≠ 0` on the slots, exponents `z` with
`z_{first q} - z_{second q} = m_q` and real parts `halfWeights S m` (that is `m_q/2` and `-m_q/2` on
the two positions of each slot and `0` elsewhere), and a compact profile `φ`
(`IsCompactProfile p φ`) whose standard section at `z` has `SlotModes` along the slots with the
weights `m`. The exponents `z(t) = z - t μ`, with `μ` the block index, are strictly dominant
whenever `Re t > Σ_q m_q` (`deform_mem_chamber`); this sufficient condition gives an open set on
which the staged formula of `stagedIntegral_of_chamber` holds. The module continues this full
staged formula from the chamber to the right half plane: for `Re t > 0` and orthogonal `g`, the
canonical Jacquet family at `(z(t), torus y · g)` equals `stagedFamily`, the staged integral
multiplied by the torus factor of the shifted exponents, the modulus `exp(torusModularLog y)` and
`haarScale r a` (`canonical_eq_stagedFamily`). It then bounds the family on vertical lines.

## Continuity

`continuous_GL_of_val` (a map into `GL_N(ℝ)` is continuous when its matrix is, by continuity of the
matrix inverse), `continuous_lowerCGL`, and `weylLong_mem` (the long Weyl element is orthogonal).

## The block deformation

- `blockWeight S i` is the block index `blockIdx i` as a real number (`blockWeight_perm`), and
  `deform S z t i = z_i - t · blockWeight S i` (`deform_re`, `deform_zero`,
  `differentiable_deform`). `deform_slot`: the deformation keeps the slot differences `m_q`.
- `halfWeights S m = slotVec (m/2) (-m/2)`; `abs_halfWeights_le` bounds it by `Σ_q m_q / 2`.
- `deform_mem_chamber`: if `m_q ≠ 0` on the slots, `Re z = halfWeights S m` and `Re t > Σ_q m_q`,
  then `deform S z t` is in
  `realSpectralChamber r`. Inside a slot the real parts differ by `m_q > 0`; between blocks the block
  index increases by at least `1`.

## The spherical majorant

- `sphExp S s = -s · blockWeight S + rhoShift`. `norm_leviIntegral_deform_le`: under the standing
  hypotheses there is `C ≥ 0` such that `‖leviIntegral S (standardSection (deform S z t) φ) b g‖ ≤ C (∏_q |b_q|^{m_q/2}) ·
  spherical (sphExp S (Re t)) g` for all `t`, `b` and `g`. This is
  `norm_leviIntegral_le_spherical`, since the block-averaged real parts of `deform S z t` are
  `-Re t · blockWeight S`.
- `spherical_sphExp_le`: for `s₁ ≤ s ≤ s₂`, `spherical (sphExp S s) ≤ spherical (sphExp S s₁) +
  spherical (sphExp S s₂)`.
- `outerPt S X g = swapGL S · lowerCGL X · w · g` (`continuous_outerPt`). For `g` orthogonal,
  `spherical_outerPt` removes `w g` and moves the slot swap through the chart
  (`permutation_mul_lowerCGL`), and `integrable_spherical_sphExp` (from
  `integrable_spherical_lowerCGL`: `sphExp S s` decreases by `1` at each step and by more when the
  block index increases), `integrable_spherical_outerPt` and `integral_spherical_outerPt` give the
  integrability of the majorant for `s > 0` and an integral independent of `g`.

## The staged integral

- `outerWeight S g X = Σ_i blockWeight S i · α_i(outerPt S X g)` (`continuous_outerWeight`).
- `stagedIntegrand S a y φ z g t X = twistChar a y (cellPt 0 X) · leviIntegral S
  (standardSection (deform S z t) φ) (slotPhase S a y) (outerPt S X g)` and `stagedIntegral` its
  integral over `X`. `stagedIntegrand_eq_exp`: it is `exp(-t · outerWeight S g X)` times its value
  at `t = 0` (`leviIntegral_sub_smul`), so it is entire in `t`.
- `stagedIntegral_of_chamber`: for a compact profile `φ`, any `z`, and `t` with `deform S z t` in
  the chamber `realSpectralChamber r`, the staged integrand is integrable and
  `canonicalJacquetFamily a hφ (deform S z t) (torus y · g)` is
  `exp(Σ_i shiftExp (deform S z t) i · y_{rev i}) · exp(torusModularLog y) · haarScale r a ·
  stagedIntegral S a y φ z g t` (`canonicalJacquetFamily_agrees`,
  `additiveJacquetIntegral_torus_mul`, `integral_cell_eq_levi`).
- `norm_stagedIntegrand_le`: under the standing hypotheses there is `C ≥ 0` such that
  `‖stagedIntegrand S a y φ z g t X‖ ≤ C P · spherical (sphExp S (Re t)) (outerPt S X g)` for all
  `a`, `y`, `g`, `t` and `X`, with `P = ∏_q |slotPhase S a y q|^{m_q/2}`
  (`norm_leviIntegral_deform_le`, `norm_twistChar`).
- `stagedIntegral_holomorphic`: under the standing hypotheses and for `g` orthogonal, the staged
  integrand is integrable for
  `Re t > 0` and the staged integral is holomorphic there (`dominatedHolomorphicIntegral`). The
  measurability comes from one point of the chamber and `stagedIntegrand_eq_exp`; near `t₀` the
  integrand is dominated by `C P (spherical (sphExp S (Re t₀/2)) + spherical (sphExp S (2 Re t₀)))`
  at `outerPt S X g` on the disk of radius `Re t₀/2` around `t₀`, by the same estimate as in
  `norm_stagedIntegrand_le` (from `norm_leviIntegral_deform_le`) and `spherical_sphExp_le`.
- `canonical_eq_stagedFamily`: under the standing hypotheses, for `g` orthogonal and `Re t > 0`,
  `canonicalJacquetFamily a hφ (deform S z t) (torus y · g) = stagedFamily S a y φ z g t`, the right
  side of `stagedIntegral_of_chamber`. Both sides are holomorphic on the connected half plane and
  agree near `t = Σ_q m_q + 1` (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`).

## The bound on vertical lines

- `prod_slotPhase`, `halfWeights_cancel`, `sum_rhoShift_rev` (`Σ_i rhoShift i · y_{rev i} =
  -torusModularLog y / 2`), `blockWeight_le` (`blockWeight S i ≤ r`) and `neg_weight_rev_le`.
- `norm_canonical_deform_le`: under the standing hypotheses, for every `a` and every `δ > 0` there
  is `A ≥ 0` with
  `‖canonicalJacquetFamily a hφ (deform S z t) (torus y · k)‖ ≤
  A exp(torusModularLog y / 2 + r δ Σ_i |y_i|)` for all `t` with `Re t = δ`, all `y` and all
  orthogonal `k`. In `stagedFamily` the half weights of `Re z` cancel against the powers
  `|slotPhase S a y q|^{m_q/2}` of the slot phases (`halfWeights_cancel`), the `ρ`-shift and the
  modulus give `torusModularLog y / 2`, and the remaining exponent is
  `-δ Σ_i blockWeight S i · y_{rev i} ≤ r δ Σ_i |y_i|`. The constant is
  `haarScale r a · C · ∏_q |a|^{m_q/2} · ∫ spherical (sphExp S δ) (lowerCGL X) dX`.
