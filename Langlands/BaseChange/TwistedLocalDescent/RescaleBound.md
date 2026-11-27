# Linear bounds for continuous additive maps commuting with one scalar

Module `Langlands.BaseChange.TwistedLocalDescent.RescaleBound`.

- `map_zpow_smul_of_map_smul`: an additive map commuting with multiplication by `c ≠ 0` commutes
  with multiplication by every integral power of `c`.
- `exists_norm_le_of_continuous_of_map_smul`: a continuous additive endomorphism `f` of a normed
  space over a nontrivially normed field, commuting with multiplication by a scalar `c` with
  `‖c‖ > 1`, satisfies `‖f x‖ ≤ C ‖x‖` for some `C ≥ 0`. Continuity at `0` gives `δ > 0` with
  `‖f y‖ < 1` for `‖y‖ < δ`; rescale `x` by a power of `c` into the shell `δ/‖c‖ ≤ ‖y‖ < δ`
  (`rescale_to_shell_zpow`).
- `exists_one_lt_norm_algebraMap`: for a finite extension `E/F` of nonarchimedean local fields
  with the module topology (normed by `LocalGalois.localNormedField`), some `a ∈ F` has
  `‖a‖_E > 1`: take `b ∈ F` with `0 < ‖b‖_F < 1`; `b^k → 0` in `F`, so in `E`, and `a = b⁻¹`.
