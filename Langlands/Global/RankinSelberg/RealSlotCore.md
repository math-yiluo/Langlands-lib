# The joint rank-two open-cell integral over the slot coordinates

Lean module: `Langlands.Global.RankinSelberg.RealSlotCore`.

This is a helper module of the proof of
`Langlands.Global.RankinSelbergGlobal.RealTemperedWhittaker.RealTemperedWhittakerBoundStatement`
(see `RealTemperedWhittakerBoundProof.md`). It states no `Prop`-valued statement; it proves lemmas
only. The content is internal and follows no literature source. Unprefixed names are in the
namespace `Langlands.Global.RankinSelbergGlobal.RealLeviStages`. `IsMode M j` (the modes
`j = ±(M + 1 + 2l)`, `l ≥ 0`), `Slot` and `coeffs` are from `RealInducedBlockBound`, and
`HasDegree` is from `RealInducedTorusCore`; `angularKernel k j x = (1 + x²)^{-(k+1)/2} e^{i j arctan x}` and its
Fourier bound `angularKernel_fourier_bound` are from `RealDiscreteReciprocalFourier`; the slot
matrices are those of `RealSlotMatrices` and `RealSlotFourier`.

The main result, `core_bound`, bounds an integral over the product of the slot coordinates, with
the slotwise phase `e^{2πi Σ_q b_q x_q}`, of a function on `O(N)` evaluated at the joint rotation
of all slots, uniformly in the remaining data. The integral factors into one-variable rank-two
open-cell integrals only term by term in the Fourier expansion along the slots.

## Lists of slots of a slot set

- `startList S` lists the starts of `S` in increasing order, without repetition
  (`startList_toFinset`, `startList_nodup`). `slotsOf S m = mkSlots (startList S) _ m` is the list
  of slots with the weights `m`; `slotsOf_pairwise`: they are pairwise disjoint;
  `length_slotsOf`.
- `modeOf L J q` is the mode that a list `J` attaches to the position `q` of a list `L`;
  `modeProd_mkSlots` writes `modeProd` over `mkSlots` as a product over the positions, and
  `allModes_withModes_mkSlots` says when all the modes are admissible (`AllModes`).

## Vanishing of the inadmissible coefficients

- `SlotModes slots u` says that every Fourier coefficient of `u` along a slot `t` of the list with an
  inadmissible mode (`¬ IsMode t.M j`) vanishes on `O(N)`. `slotModes_blockFourierCoefficient`
  and `slotModes_coeffs`: for continuous `u`, Fourier coefficients along slots disjoint from those
  of the list keep this property.
- `coeffs_withModes_eq_zero`: if `u` is continuous, the slots are pairwise disjoint, `u` has
  `SlotModes` along them and one mode of `J` is inadmissible, then `coeffs (withModes slots J) u`
  vanishes on `O(N)`. `hasDegree_congr`, `slotModes_congr`: both
  properties only depend on the values on `O(N)`.

## The angular kernels

- `norm_angularKernel`: `‖angularKernel k j x‖ = ρ(x)^{-(k+1)}`, where
  `ρ(x) = cellNorm x = √(1 + x²)`; `continuous_angularKernel`,
  `integrable_angularKernel` (for `k ≠ 0`).
- `angularKernel_fourier_half`: for `k ≠ 0` and an admissible mode `j`, the Fourier transform is
  bounded by `C |y|^{k/2}` (`angularKernel_fourier_bound` with exponent `k/2`). `angConst k j` is
  such a constant (and `0` when `k = 0` or `j` is inadmissible), with
  `norm_fourier_angularKernel_le` (for `k ≠ 0` and admissible `j`).
- `integral_angularKernel_phase`: the integral of the angular kernel against `e^{2πi c t}` is its
  Fourier transform at `-c`. `integral_angularKernel_affine`: for `s > 0`, the integral of the
  angular kernel at `(t + c) s` against `e^{2πi b t}` is `s⁻¹ e^{-2πi b c}` times its Fourier
  transform at `-b / s`.

## The core bound

- `arcVec S x` is the vector of the angles `arctan x_q`, and `affineCoord S c s x` the
  coordinates `(x_q + c_q) s_q`.
- `coreIntegrand S m u k b c s x` is
  `∏_q ρ(y_q)^{-(m_q + 1)} · u(rot S (arctan y) · k) · e^{2πi Σ_q b_q x_q}` with
  `y = affineCoord S c s x`.
- `slotKernel_eq` and `coreIntegrand_eq`: let `u` be continuous, right `O(N)`-finite and of degree
  at most `D` along the slots, and `k ∈ O(N)`. By `eq_sum_rotProd`, the core integrand equals
  `(2π)^{-n_S} Σ_J coeffs (withModes (slotsOf S m) J) u k · coreTerm J x`, where `n_S` is the number
  of slots (`length_slotsOf`: the length of `slotsOf S m` is the cardinality of `S.starts`), the
  finite sum runs over the mode lists `J` of `modeLists D n_S`, and `coreTerm J x` is the product
  over the slots of the one-variable functions
  `angularKernel (m q) (j_q) ((x_q + c_q) s_q) e^{2πi b_q x_q}`.
  For `s_q > 0` on the slots, `integral_coreTerm` integrates each such product as a product of
  one-variable integrals (`integral_fintype_prod_volume_eq_prod`, `integral_angularKernel_affine`);
  `integrable_coreTerm` gives integrability when moreover `m_q ≠ 0` on the slots.
- `coreConstant S m D B = max B 0 · Σ_J ∏_q angConst (m q) (j_q)`, nonnegative.
- `core_bound`: let `m_q ≠ 0` on the slots, `u` continuous, right `O(N)`-finite, of degree at most
  `D` along the slots, with `SlotModes` and `‖u‖ ≤ B` on `O(N)`, and `k ∈ O(N)`, `s_q > 0`. Then the
  core integrand is integrable and
  `‖∫ coreIntegrand‖ ≤ coreConstant S m D B · ∏_q s_q⁻¹ |b_q / s_q|^{m_q/2}`. The terms with an
  inadmissible mode vanish (`coeffs_withModes_eq_zero`); in every other term the coefficient is
  bounded by `(2π)^{n_S} B` (`norm_coeffs_le_of_mem`), which cancels the prefactor `(2π)^{-n_S}`,
  and the integral of `coreTerm J` by the product of the Fourier bounds of its angular kernels.
  The constant does not depend on `k`, `b`, `c` or `s`.
