# Rational evaluation at regular points

Worker 31. This internal helper module has namespace
`Langlands.RankinSelberg.RationalEvaluation`. Its results hold over any field
`K : Type u` and support the JPSS gamma construction without adding analytic
hypotheses. Their provenance is elementary algebra of Mathlib's reduced
numerator and denominator; no external mathematical assertion is postulated.
The only project substitution used is the published `RationalReflection.subst`.

## Regularity

`RegularAt R z : Prop` means `R.denom.eval z != 0`. This is a predicate on the
reduced denominator, so it allows zeros that canceled from another presentation
of `R`. Mathlib's total evaluation is not a ring homomorphism on all rational
functions at a fixed point; the following hypotheses are used explicitly.

`RegularAt.of_dvd` proves regularity when `R.denom` divides a polynomial
nonzero at `z`. Polynomial evaluation sends a divisor of a vanishing value to
a vanishing multiple, which gives the proof by contradiction.
`RegularAt.polynomial` uses the constant reduced denominator of a polynomial.
`RegularAt.add` and `RegularAt.mul` use Mathlib's divisibility of the reduced
denominator by the product of the two input denominators.
`eval_add` and `eval_mul` specialize Mathlib's evaluation lemmas to the
identity coefficient map under these regularity hypotheses.

`RegularAt.of_eval_ne_zero` uses Mathlib's theorem that a nonzero totalized
evaluation has a nonzero denominator value. `RegularAt.inv` assumes the
evaluation of `R` is nonzero. Then `R` and its numerator value are nonzero,
and the reduced denominator of the inverse divides the original numerator.
`eval_inv` applies regular multiplication to `R * R^(-1) = 1` and cancels the
nonzero value. `eval_div` combines multiplication and inversion; it requires
regularity of the numerator rational function and a nonzero evaluated
denominator rational function.

`RegularAt.pow` and `eval_pow` follow by induction on natural exponents,
using regular multiplication. `RegularAt.zpow` and `eval_zpow` assume a
nonzero evaluated base and split an integer exponent into a nonnegative or
negative-successor case. The latter uses the proved inverse and natural-power
lemmas. The stronger nonzero hypothesis is retained uniformly for all integer
exponents.

## Polynomial evaluation and reciprocal substitution

`RegularAt.aeval` and `eval_aeval` prove that substituting a regular rational
function into a polynomial preserves regularity and commutes with evaluation.
The proof uses polynomial induction by addition and monomials, rewriting a
monomial as a constant times a power of `X`, then using the preceding lemmas.

For a unit `c : K^*` and `z != 0`, `regular_reflectedVariable` and
`eval_reflectedVariable` prove regularity and the value `c/z` for the shared
rational variable `c/X`. They use regular constants, inversion of `X`, and
division evaluation.

`regular_subst` and `eval_subst` additionally assume `RegularAt R (c/z)`.
They respectively prove regularity of `RationalReflection.subst c R` at `z`
and the equality

\[
\operatorname{eval}_z(\operatorname{subst}_c R)
  =\operatorname{eval}_{c/z}(R).
\]

Both proofs present `R` as `R.num / R.denom`, use that substitution is an
algebra homomorphism and agrees with polynomial substitution, and apply the
regular polynomial and division lemmas. The assumed original reduced
denominator value is exactly the nonzero value needed after substitution.
These are sufficient regularity criteria; the module does not assert their
converses or infer analytic continuation from totalized evaluation.
