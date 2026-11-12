# Complex powers of the idelic norm

Author: Worker 34. This module is internal infrastructure derived from the
Library's actual idelic norm and the complex exponential. It assumes no
arithmetic existence theorem. It supplies the factor `‖·‖^{(n-1)/2}` of
Harris's twisting character (Harris 1998, Erratum (E.1); see
`Langlands/Galois/HarrisTwistingCharacter.md`). There the exponent is a
half-integer when `n` is even, so the published imaginary powers
`HeckeCharacter.unitaryNormPower` do not cover it.

## Definitions

For a number field `F` and a complex number `s`:

- `HeckeCharacter.normPowerValue F s : IdeleClasses F →* ℂ` sends an idele
  class `a` to `exp(s · log |a|)`. Here `|a|` is the published normalized idelic
  norm `IdeleAbsoluteValue.ideleClass F a`, a positive real number. The
  published norm already uses the product formula to descend to idele classes.
  Multiplicativity comes from `Real.log_mul` and `Complex.exp_add`.
- `HeckeCharacter.normPower F s : HeckeCharacter F` is the same map with values
  in `ℂˣ`, written `‖·‖^s`. It is continuous because the norm, the real
  logarithm on positive reals and the complex exponential are continuous
  (`continuous_normPowerValue`).

## Proved properties

- `normPower_apply`: the defining formula `‖a‖^s = exp(s · log |a|)`.
- `normPower_ofReal_apply`: for real `s` the value is the real power
  `|a|^s` (`Real.rpow_def_of_pos`), the usual meaning of `|·|_A^{(n-1)/2}`.
- `normPower_zero` and `normPower_add`: `‖·‖^0 = 1` and
  `‖·‖^{s+t} = ‖·‖^s · ‖·‖^t`.
- `unitaryNormPower_eq_normPower`: the published imaginary powers
  `unitaryNormPower F t` (from `Langlands.Global.HeckeNormTwist`) are the case
  `s = t · i`.
- `normPower_finiteComponent`: at a finite place `v` the local component sends
  `a ∈ F_v^×` to `exp(s · log ‖a‖_v)`, with the actual completion norm. The proof
  uses the published `IdeleAbsoluteValue.coe_ideleClass_finiteClassInclusion`.
- `normPower_isUnramifiedAt`: `‖·‖^s` is trivial on the integral units of every
  completion. An integral unit has valuation `1`, so its norm is `1`.

The module states and proves nothing about algebraicity (type `A₀`) of
`‖·‖^s`.
