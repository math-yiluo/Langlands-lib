# Existence of real parts of split-centre characters

Author: Worker 23.

This module proves that every character of `(F^×)^r` with open kernel has a
real part in the sense of the published
`Langlands.PadicField.TopologicalData.IsRealPartOf`
(`Langlands.Representation.Exponents.Jacquet`): there is `x : Fin r → ℝ` with
`‖χ a‖ = ∏ i, T.normalizedAbs (a i) ^ x i` for all `a`. The published
`IsRealPartOf.eq` gives uniqueness; this module supplies existence. All results
use the actual topology `T.topology`, the actual normalized absolute value
`T.normalizedAbs` and the chosen uniformizer `T.uniformizerUnit`
(`Langlands.Group.GL.UnramifiedCharacter`). No continuity of `χ` for the
topology of `ℂˣ` is assumed; only openness of its kernel.

This is an internal helper for the maximal-cone proof (task b291a31b): the
cone selection needs a real part for every dual Jacquet exponent. It is the
familiar fact that a character of `F^×` with open kernel is a unitary character
times a real power of `|·|`. The Lean proof is the direct argument below.

## One coordinate

`norm_eq_one_of_isOpen_ker T χ hχ hu`: if `χ : F.Carrierˣ →* ℂˣ` has open
kernel and `u` lies in the kernel `K` of `T.normalizedAbsUnits` (the norm-one
units), then `‖χ u‖ = 1`.

- `K` is compact by the published
  `CuspidalSupport.isCompact_ker_normalizedAbsUnits T`.
- `U = χ.ker.subgroupOf K` is open in `K` (`Subgroup.subgroupOf_isOpen`), so
  `K ⧸ U` is finite (`Subgroup.quotient_finite_of_isOpen`).
- Hence `u ^ U.index ∈ U` (`Subgroup.pow_index_mem`), so
  `χ u ^ U.index = 1` and `‖χ u‖ ^ U.index = 1` with `U.index ≠ 0`. A
  nonnegative real whose nonzero power is `1` equals `1`
  (`pow_eq_one_iff_of_nonneg`).

`norm_eq_zpow_ord_of_isOpen_ker T χ hχ a`: for every unit `a`,
`‖χ a‖ = ‖χ ϖ‖ ^ T.ord a`, where `ϖ = T.uniformizerUnit`. Put `k = T.ord a`
and `u = a * ϖ ^ (-k)`. Then `T.normalizedAbs u = q^(-k) * q^k = 1`, by
`normalizedAbs_mul`, `normalizedAbs_of_ne_zero` and the published
`LocalFactor.PadicAbelian.uniformizerUnit_zpow_abs`, where
`q = T.residueCardinality`. So `u ∈ K`, and `a = u * ϖ ^ k` gives the claim
from the previous theorem.

`norm_eq_normalizedAbs_rpow_of_isOpen_ker T χ hχ a`: for every unit `a`,
`‖χ a‖ = T.normalizedAbs a ^ (-logb q ‖χ ϖ‖)`. Write
`T.normalizedAbs a = q ^ (-k)` and `‖χ ϖ‖ = q ^ (logb q ‖χ ϖ‖)`
(`Real.rpow_logb`, using `1 < q` from `one_lt_residueCardinality_real` and
`‖χ ϖ‖ > 0`), then compare exponents with `Real.rpow_mul`.

## Products

`exists_isRealPartOf T χ hχ`: for `χ : (Fin r → F.Carrierˣ) →* ℂˣ` with open
kernel, `∃ x, T.IsRealPartOf χ x`.

Let `χ_i = χ ∘ MonoidHom.mulSingle _ i`. Its kernel is the preimage of `χ.ker`
under the continuous map `Pi.mulSingle i` (`continuous_mulSingle`), so it is
open. Take `x i = -logb q ‖χ_i ϖ‖`. Since `a = ∏ i, Pi.mulSingle i (a i)`
(`Finset.univ_prod_mulSingle`), `χ a = ∏ i, χ_i (a i)`, and the norm of the
product is the product of the coordinate formulas above.
