# Complete valued fields are henselian: proof

Author: Worker 105.

Proof of `Langlands.AlgebraicGeometry.PointTopology.CompleteHenselianValuedFieldStatement.{u}`:
every complete nontrivially normed field is a henselian valued field
(`IsHenselianValuedField`). This is the fact presupposed by Conrad's remark on printed p.14 of
*Weil and Grothendieck approaches to adelic points* (December 31, 2011) that complete ground
fields suffice. The entry theorem is `completeHenselianValuedField`.

## Route

Uniqueness of extensions holds over every complete field (`absoluteValue_eq` in
`CompleteHenselianValuedField`). For existence there are two cases.

- **Non-archimedean** (`IsUltrametricDist K`): the spectral norm is the extension
  (`isHenselianValuedField_of_isUltrametricDist`, module `CompleteHenselianValuedField`).
- **Archimedean**: some natural number has norm `> 1`
  (`isUltrametricDist_iff_forall_norm_natCast_le_one`). This module shows that `K` has a ring
  map `φ : K → ℂ` with `‖x‖ = ‖φ x‖ ^ s` for some `0 < s ≤ 1`. Then the extension to an algebraic
  `L` is `y ↦ ‖σ y‖ ^ s`, for an embedding `σ : L → ℂ` over `K`.

## Declarations

Namespace `Langlands.AlgebraicGeometry.PointTopology.CompleteHenselian`:

- `isHenselianValuedField_of_rpow`: a complete field with `φ : K →+* ℂ`, `‖x‖ = ‖φ x‖ ^ s` and
  `0 < s ≤ 1` is henselian. `IsAlgClosed.lift` embeds `L` in `ℂ`. The function `‖σ y‖ ^ s` is
  an absolute value because `(a + b) ^ s ≤ a ^ s + b ^ s` for `s ≤ 1`.
- `charZero_of_one_lt_norm_natCast`: if some `‖(n : K)‖ > 1`, then `K` has characteristic zero.
  In characteristic `p` we have `n ^ p = n` (`ZMod.pow_card`), so `‖n‖ ≤ 1`.
- `ratAbs`, `ratAbs_apply`: the norm restricted to `ℚ`.
- `exists_rpow_of_not_ultrametric`: in the archimedean case, `‖q‖ = |q| ^ s` on `ℚ` with
  `0 < s ≤ 1`. This is Ostrowski's theorem (`Rat.AbsoluteValue.equiv_real_of_unbounded` and
  `AbsoluteValue.isEquiv_iff_exists_rpow_eq`). The bound `s ≤ 1` comes from `‖2‖ ≤ 2`.
- `rpow_norm_add_le`: **Artin's argument**. If `‖(m : K)‖ = m ^ s` for natural numbers `m`,
  `s * t = 1` and `t ≥ 1`, then `‖·‖ ^ t` is subadditive. Expand `(x + y) ^ n` by the binomial
  theorem and use the power-mean inequality (`Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg`).
  This gives `(‖x + y‖ ^ t) ^ n ≤ (n + 1) ^ (t - 1) (‖x‖ ^ t + ‖y‖ ^ t) ^ n`, and exponential
  growth beats polynomial growth (`tendsto_pow_const_div_const_pow_of_one_lt`).
- `uniformContinuous_ratCast`, `realHom`, `realHom_ratCast`, `continuous_realHom`,
  `norm_realHom`: by completeness the inclusion of `ℚ` extends to a ring map `ℝ → K`
  (`IsDenseInducing.extendRingHom`) with `‖r‖ = |r| ^ s`.
- `archAbs` (with `archAbs_apply`, `archAbs_realHom`, `norm_eq_archAbs_rpow`): the absolute value
  `‖·‖ ^ (1/s)` on `K`, which restricts to `|·|` on `ℝ`.
- `exists_complex_rpow`: `WithAbs archAbs` is a normed `ℝ`-algebra, so Gelfand–Mazur
  (`NormedAlgebra.Real.nonempty_algEquiv_or`) identifies it with `ℝ` or `ℂ` as `ℝ`-algebras.
  For `ℝ` the identification sends `x` to the real number `r` with `x = r`, so
  `archAbs x = |r|`. For `ℂ`, the transported absolute value extends `|·|` on `ℝ`. It is
  therefore the usual one, by uniqueness over the complete field `ℝ`. In both cases
  `‖x‖ = ‖φ x‖ ^ s`.
- `isHenselianValuedField_of_not_isUltrametricDist`: complete archimedean fields are henselian.

Namespace `Langlands.AlgebraicGeometry.PointTopology`:

- `completeHenselianValuedField : CompleteHenselianValuedFieldStatement.{u}`.

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Sources

- Conrad, registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
  `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, printed p.14.
- The archimedean case uses the standard route via Ostrowski's theorem on `ℚ`, Artin's criterion
  for absolute values and the Gelfand–Mazur theorem, as available in Mathlib.
