# Polynomial growth of the archimedean determinant factor of a Hecke character

Author: Worker 5136.

This internal module proves that, for every Hecke character `χ` of a number
field `K` and every rank `n`, the archimedean determinant factor
`g ↦ χ(det (ofInfinite g))` has polynomial growth on the archimedean matrix
group, in the sense of the Library's `ArchimedeanGL.HasPolynomialGrowth`: it is
bounded by `C · matrixHeight g ^ d`. No finite-order hypothesis is used. For a
finite-order `χ` the factor has absolute value one; for a general `χ` it does
not, and this module gives the replacement bound.

## Characters of the units of the mixed space

- `exp_mixedSpace_fst_apply`, `exp_mixedSpace_snd_apply`: the exponential of
  the mixed space `mixedSpace K = (real places → ℝ) × (complex places → ℂ)` is
  computed componentwise by `Real.exp` and `Complex.exp`. The proof applies
  `NormedSpace.map_exp_of_mem_ball` to the continuous evaluation ring maps.
- `units_fst_mul_inv`, `units_snd_mul_inv`, `units_fst_ne_zero`,
  `units_snd_ne_zero`: every component of a unit `u` is nonzero, with inverse
  the component of `u⁻¹`.
- `mixedLog u` is the element whose real components are `log |u_v|` and whose
  complex components are the principal logarithms `log u_w`.
- `sign_mul_sign_eq_one`: the sign part `s = u · (banachExpUnit (mixedLog u))⁻¹`
  satisfies `s · s = 1`. At a real place `s_v = u_v / |u_v|`, so
  `s_v² = 1`; at a complex place `s_w = 1`.
- `abs_log_le_log_of_le`: if `y > 0` and `y, y⁻¹ ≤ M`, then `|log y| ≤ log M`.
- `unitHeight u` is `max 1 (max ‖u‖ ‖u⁻¹‖)`, with `one_le_unitHeight`,
  `norm_le_unitHeight` and `norm_inv_le_unitHeight`.
- `norm_mixedLog_le`: `‖mixedLog u‖ ≤ log (unitHeight u) + π`. Each
  component of `u` and of `u⁻¹` has norm at most `unitHeight u`. At a real
  place this bounds `|log |u_v||`; at a complex place the real part of
  `log u_w` is `log |u_w|` and its imaginary part, the argument, has absolute
  value at most `π`.
- `exists_norm_unitsCharacter_le`: every continuous character
  `ψ : (mixedSpace K)ˣ →ₜ* ℂˣ` satisfies `‖ψ u‖ ≤ C · unitHeight u ^ d` for
  some `C ≥ 0` and `d : ℕ`. Write `u = s · banachExpUnit (mixedLog u)`. Since
  `s² = 1`, `‖ψ s‖ = 1`. By `exists_unitsCharacter_exp` (module
  `ArchimedeanCharacterSmoothness`), `ψ (banachExpUnit a) = exp (L a)` for a
  continuous real-linear `L`. Hence
  `‖ψ u‖ = exp (Re L (mixedLog u)) ≤ exp (‖L‖ (log (unitHeight u) + π))`,
  which is `exp (‖L‖ π) · unitHeight u ^ ‖L‖` and is at most
  `exp (‖L‖ π) · unitHeight u ^ ⌈‖L‖⌉` because `unitHeight u ≥ 1`.

## The determinant

- `norm_det_le_factorial_mul_pow`: over a normed commutative ring, if every
  entry of an `m × m` matrix (`m > 0`) has norm at most `B`, then
  `‖det A‖ ≤ m! · B ^ m`. The proof bounds each of the `m!` terms of the
  Leibniz formula.
- `ArchimedeanGL.norm_entry_le`: each entry of an archimedean matrix has norm
  at most the matrix norm (the `L∞` operator norm used by `matrixHeight`).
- `ArchimedeanGL.norm_det_le`: `‖det A‖ ≤ n! · ‖A‖ ^ n` for `n > 0`.
- `ArchimedeanGL.unitHeight_det_le`: for `n > 0`, the height of the
  determinant of the coordinates of `x` is at most `n! · matrixHeight x ^ n`.
  The inverse of the determinant is the determinant of the inverse matrix.
- `ArchimedeanGL.HasPolynomialGrowth.mul`: a product of two functions of
  polynomial growth has polynomial growth.

## The determinant factor

`HeckeCharacter.hasPolynomialGrowth_adelicDeterminant_ofInfinite`: for every
Hecke character `χ` and rank `n`, the function
`g ↦ χ(det (ofInfinite g))` has polynomial growth. For `n = 0` the determinant
is `1`. For `n > 0`, `adelicDeterminant_ofInfinite_coordinates` rewrites the
value as `mixedCharacter χ (det x)` with `x` the coordinates of `g`, and the
two previous bounds give `C · n! ^ d · matrixHeight g ^ (n d)`.

Provenance: internal. These are standard estimates for continuous characters
of real Lie groups, proved here directly through the decomposition of a unit
into a sign and an exponential. They are an ingredient for Henniart (2000),
§2.2, which twists by arbitrary quasicharacters. No correspondence with a
particular passage of the literature is claimed.
