# The Levi-staged Jacquet integral of a slot set

Lean module: `Langlands.Global.RankinSelberg.RealSlotStaged`.

This is a helper module of the proof of
`Langlands.Global.RankinSelbergGlobal.RealTemperedWhittaker.RealTemperedWhittakerBoundStatement`
(see `RealTemperedWhittakerBoundProof.md`). It states no `Prop`-valued statement; it proves lemmas
only. The content is internal and follows no literature source. Unprefixed names are in the
namespace `Langlands.Global.RankinSelbergGlobal.RealLeviStages`. `additiveJacquetIntegral a f g` is
the Jacquet integral `∫_N f(w n g) ψ_a(n) dn` with the measure `upperStepHaar r a` (module
`RealGodementAdditiveJacquet`), `conjTorus` is the conjugation by `torus y` of `RealIwasawa`,
`torusModularLog` and `map_conjTorus` are from `RealToralQuotientDensity`, and `w` is the long Weyl
element. The open cell coordinates are those of `RealSlotCellMeasure` and `RealSlotOpenCell`.

The module writes the twisted open cell integral of a function as an iterated integral: first
over the coordinates inside the blocks of the slot Levi subgroup (the inner Levi integral of
`RealSlotLevi`), then over the opposite unipotent radical.

## The torus twist of the open cell

- `twistChar a y u` is the standard character `ψ_a` at `torus y · u · torus y⁻¹`
  (`norm_twistChar`, `continuous_twistChar`, `twistChar_mul`).
- `weyl_torus_conj`: `w u (torus y · g) = torus (y ∘ rev) · (w · conjTorus (-y) u · g)`.
- `additiveJacquetIntegral_torus_mul`: for a compact profile `φ` (`IsCompactProfile p φ`) and `z` in
  the chamber `realSpectralChamber r`, the integrand
  `v ↦ standardSection z φ (w v g) · twistChar a y v` is integrable and
  `additiveJacquetIntegral a (standardSection z φ) (torus y · g) =
  exp(Σ_i shiftExp z i · y_{rev i}) · exp(torusModularLog y) · ∫ standardSection z φ (w v g) ·
  twistChar a y v dv`. Here `u` is the original variable and `v = conjTorus (-y) u` the new one:
  the pushforward of Haar measure under `u ↦ conjTorus (-y) u` is `exp(torusModularLog y)` times
  Haar measure (`map_conjTorus`); equivalently, the inverse substitution `u = conjTorus y v` gives
  `du = exp(torusModularLog y) dv`. The torus factor is pulled out with
  `standardSection_unipotent_torus_mul`.

## The phase of the block coordinates

- `cellPt_zero_entry`: the entry `(i, j)` of `cellPt Z 0` is `lowerM cl Z (rev i) (rev j)`.
  `conjTorus_entry` computes the entries of `conjTorus y u`; `realScaledCharacter_complex` writes
  `ψ_a(x) = exp(2πi a x)`.
- `sum_superdiag_slots` reindexes the superdiagonal entries `(i, i + 1)` by the slots `r - 1 - i`.
- `slotPhase S a y q = a · exp(y_{rev(q+1)} - y_{rev q})` on the slots and `0` elsewhere
  (`slotPhase_coe`).
- `twistChar_cellPt_block`: for the block function `blockIdx` of the slot set,
  `twistChar a y (cellPt Z 0) = exp(2πi Σ_q slotPhase S a y q · slotOfM Z q)`
  (`sum_superdiag_cellPt_block`).

## The open cell integral in Levi stages

- `integral_cellPt_block`: for every `X`,
  `∫_Z f(w · cellPt Z X · g) twistChar a y (cellPt Z X) dZ = twistChar a y (cellPt 0 X) ·
  leviIntegral S f (slotPhase S a y) (swapGL S · lowerCGL X · w · g)`. Indeed
  `w · cellPt Z X = swapGL S · unip S (ext (slotOfM Z)) · swapGL S · lowerCGL X · w`
  (`weylLong_mul_cellPt`, `lowerMGL_eq`), and the character splits over `cellPt_mul`.
- `integral_cell_eq_levi`: if the twisted open cell integrand of a continuous `f` is integrable,
  then the outer integrand `X ↦ twistChar a y (cellPt 0 X) · leviIntegral S f (slotPhase S a y)
  (swapGL S · lowerCGL X · w · g)` is integrable and the open cell integral is `haarScale r a`
  times its integral (`integral_upperStepHaar_eq`, `Integrable.integral_prod_right`).

## The deformation of the exponents along the block index

- `standardSection_sub_smul`: for every profile `φ`, real weight `μ` and `t ∈ ℂ`,
  `standardSection (z - t μ) φ g = exp(-t Σ_i μ_i α_i(g)) ·
  standardSection z φ g` (`standardSection_eq`).
- `sum_mul_alpha_swapGL_unip_mul`: a weight `μ` with `μ ∘ perm = μ` has
  `Σ_i μ_i α_i(swapGL S · unip S x · g) = Σ_i μ_i α_i(g)` (`alpha_swapGL_unip_mul`,
  `sum_mul_perm_add_cellExponent`).
- `leviIntegral_sub_smul`: hence, for every profile `φ` and every weight `μ` with `μ ∘ perm = μ`,
  `leviIntegral S (standardSection (z - t μ) φ) b g = exp(-t Σ_i μ_i α_i(g)) ·
  leviIntegral S (standardSection z φ) b g`.
