# The entries of a rational matrix relating two Siegel points

Module: `Langlands.Global.SiegelFiniteness.Entries`. Provenance: internal.

- `realScale_mul_eq_of_fst`: if the archimedean component of `z` is zero, `realScale s · z`
  does not depend on `s`.
- `fst_mul_mul_eq_zero`: the archimedean component of `p q r` vanishes if that of `q` does.
- `entries_mem` (**bounded entries**): suppose the key inequality holds with `β ≥ 0` for the
  compact set `Q₁`, and `γ h = h'` with `h = N diag(ω) A_x κ`, `h' = N' diag(ω') A_{x'} κ'`
  as in `exists_siegel_data` (`N, N' ∈ ΩN`, `ω, ω' ∈ C^n`, `κ, κ'` standard compact, `x, x'`
  in the chamber with constant `K ≥ 0`, `A_x⁻¹ h, A_{x'}⁻¹ h' ∈ Q₁`). Then every entry of
  `γ` lies in `entrySet F n ΩN C Λ` with `Δ = β + 2nK`, `G = Δ + β + 2nK`,
  `Λ = Δ + nK + nG`.

  Proof: the key inequality for `(γ, h, h')` and for `(γ⁻¹, h', h)` gives
  `(γ⁻¹)_{tj} ≠ 0 → x'_j ≤ x_t + β` and `γ_{tj} ≠ 0 → x_j ≤ x'_t + β`; with
  `exists_lowerLeft_ne_zero` and `le_add_of_key`, `x'_i ≤ x_i + Δ`. A drop of `x` larger than
  `G` at `q` makes `γ` vanish in rows `≥ q`, columns `< q` (`not_of_drop`), hence
  `m = κ' κ⁻¹` too (`isBlockUpper_compactPart`). For each `(a, b)`, `le_or_exists_drop` gives
  either `x'_a - x_b ≤ Λ`, so `M_{ab} = realScale(e^{x'_a - x_b}) (ω'_a m_{ab} ω_b⁻¹)` lies in
  `middleSet` with `ρ ∈ [0, e^Λ]`, or a drop at some `q` with `a < q ≤ b`, so the archimedean
  component of `m_{ab}` vanishes (`infinite_entry_eq_zero`) and `M_{ab}` equals the value with
  `ρ = 0`. Finally `γ = N' M N⁻¹` and `N⁻¹ = adj N`.
