# The tempered bound of the canonical Jacquet family of a slot profile

Lean module: `Langlands.Global.RankinSelberg.RealSlotTemperedBound`.

This is a helper module of the proof of
`Langlands.Global.RankinSelbergGlobal.RealTemperedWhittaker.RealTemperedWhittakerBoundStatement`
(see `RealTemperedWhittakerBoundProof.md`). It states no `Prop`-valued statement; it proves lemmas
only. Unprefixed names are in the namespace `Langlands.Global.RankinSelbergGlobal.RealLeviStages`.
The interpolation follows the proof of `realTemperedWhittakerBound_characterList` in the module
`RealTemperedCharacterBound`, with the deformation and the line bound of `RealSlotStagedFamily`.

- `neg_half_torusModularLog_le`: `-torusModularLog y / 2 ≤ r Σ_i |y_i|`.
- `canonical_tempered_slot_bound`: let `S` be a slot set with weights `m_q ≠ 0`, `z` exponents with
  `z_{first q} - z_{second q} = m_q` and `Re z = halfWeights S m`, and `φ` a compact profile whose
  standard section has `SlotModes`. Then for every `ε > 0` there is `C ≥ 0` with
  `‖canonicalJacquetFamily a hφ z (torus y · k)‖ ≤ C exp(torusModularLog y / 2 + ε Σ_i |y_i|)` for
  all `y` and all orthogonal `k`.

The proof applies `smallExponentialAtZero_of_rightBoundary` (module `SmallExponentialBoundary`) to
`F(t)(y, k) = exp(-torusModularLog y / 2) · canonicalJacquetFamily a hφ (deform S z t) (torus y · k)`,
which is entire in `t`. On the closed disk of radius `2` the family has uniform polynomial growth in
the matrix height (`RealUnequalFamily.exists_uniform_derivativeGrowth`), hence an exponential bound
in `Σ_i |y_i|` (`RealWhittakerGauge.realMatrixHeight_torus_mul_pow_le`,
`neg_half_torusModularLog_le`). On each line `Re t = δ ∈ (0, 1)` the bound
`norm_canonical_deform_le` gives the loss `exp(r δ Σ_i |y_i|)`. The boundary lemma gives the loss
`exp(ε Σ_i |y_i|)` at `t = 0`, where `deform S z 0 = z`.
