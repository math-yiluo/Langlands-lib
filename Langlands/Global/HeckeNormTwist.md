# Unitary norm powers and unramified local character prescription

This module is internal infrastructure derived from the Library's actual idelic
norm and elementary complex exponential. It introduces no arithmetic existence
assumption. It supports removing an unramified unitary twist in the proof of
`Langlands.Global.HenniartGlobalizationStatement`.

For a number field `F` and real `t`,
`HeckeCharacter.unitaryNormPower F t` is the continuous character on the actual
idele-class group with value `exp(i t log |a|)`. The norm is the existing
`IdeleAbsoluteValue.ideleClass`; its descent already uses the product formula.
The imaginary exponential has absolute value one, so this Hecke character is
unitary. Its component at a finite place sends `a` to
`exp(i t log ‖a‖)`, using the actual completion norm, and is trivial on integral
units at every finite place.

`finiteComponent_ext_of_generator` proves that two characters trivial on
integral units agree if they agree on an element whose valuation is
`WithZero.exp 1`. For each nonzero local element, the integer logarithm of its
valuation gives the exponent of that generator; division by its corresponding
power lies in the integral units.

`exists_unitaryNormPower_finiteComponent` then realizes any supplied unitary
character trivial on integral units as a component of a global norm power.
Surjectivity of the actual adic valuation supplies a generator `b` with
`‖b‖ > 1`. The proof chooses
`t = arg(η(b)) / log ‖b‖`. The polar identity for a unit complex number gives
agreement at `b`, and the preceding character comparison gives agreement on
the full local multiplicative group.

The final theorem `exists_unitary_unramified_extension` packages the result as
a unitary Hecke character unramified at every finite place with exactly the
prescribed component at the selected place. No restriction of finite order is
placed on the local or global character.

The public inputs are `IdeleAbsoluteValue.ideleClass`,
`coe_ideleClass_finiteClassInclusion`, Mathlib's
`HeightOneSpectrum.valuedAdicCompletion_surjective`, the characterization of
integral units by valuation one, the comparison between norms and valuations,
and `Complex.norm_mul_exp_arg_mul_I`. The final globalization target is not
proved in this module.
