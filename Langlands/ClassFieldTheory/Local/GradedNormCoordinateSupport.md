# Literal quotients for graded norm coordinates

Worker 96 authored this internal support module. It imports the integral norm
and elementary residue support in `PrimeGradedNormSupport`; it does not prove
`PrimeRamifiedGradedNorm` or any trace-image or norm-expansion formula.

For arbitrary topological data `T` and a supplied order-one uniformizer `π`,
`idealQuotient n a ha` is the integer with literal field value `a / π^n`, where
`ha` says that `a` lies in the nth power of the actual maximal ideal.
`idealQuotient_integral` follows by factoring `a` using the existing
principal-ideal description. `uniformizer_pow_mul_idealQuotient` reconstructs
the numerator. Cancelling the nonzero uniformizer power in divisibility proves
`residue_idealQuotient_eq_zero_iff`: reduction of the quotient is zero exactly
when the numerator lies in the next ideal power. These results include `n=0`
and zero numerators.

`residue_ne_zero_of_ord_eq_zero` assumes that the integer has nonzero field
value and order zero. Its inverse is integral by the normalized absolute-value
criterion, so it is an integer-ring unit and has nonzero residue. The nonzero
hypothesis matters because the existing convention assigns order zero to zero.

The extension lemmas retain arbitrary independent field universes, the actual
supplied algebra and compatible Padic scalar tower, and finite dimension.
`integerNorm_mul` and `integerNorm_pow` expose multiplicativity of the existing
integer-valued norm; they need no total-ramification assumption.

Under the explicit total-ramification identity, `integerNorm_mem_pow` factors a
source integer as a uniformizer power times an integer. The norm of that
uniformizer again has order one by `PrimeGradedNorm.ord_norm`. Multiplicativity
then proves that the norm lies in the same-index target maximal-ideal power.
`norm_coefficient` applies this fact to the nth power of any supplied source
uniformizer and divides by the nth power of any supplied target uniformizer.
The resulting integer has exactly the field value `N(πL)^n / πF^n`. Its field
value is nonzero and its order is zero, so its residue is nonzero. This includes
all natural n and does not require a prime degree or Galoisness.

With Galoisness, `norm_term_coordinate` considers an actual source filtration
unit `x`, an integer `a` with field value `N(πL)^n / πF^n`, and an integer `q`
with field value `N(x-1) / πF^n`. It proves

```text
r(residue(q)) = r(residue(a)) * residue(unitCoefficient(πL,n,x))^[L:F].
```

Here `r` is the actual forward residue map. Factoring `x-1` as the source
uniformizer power times its literal unit coefficient identifies `q` with
`a * integerNorm(unitCoefficient(πL,n,x))`. The equality follows by reducing
and applying `PrimeGradedNorm.residue_norm`. This last lemma assumes the two
specified integers and their value equalities; it does not assert the
integrality of these expressions for an arbitrary denominator `πF`.
`norm_coefficient` supplies the first witness for order-one denominators, and
`integerNorm_mem_pow` plus `idealQuotient` supplies the second. The lemma alone
does not identify the entire norm of `x` with its norm term.

These are internal algebraic consequences of the imported coordinate and norm
constructions. The literal norm coefficient and its contribution to the
positive graded formula follow the calculation in Jean-Pierre Serre,
*Local Fields*, V.3, Proposition 5, printed p.85 / PDF p.92, registered as
`serre-1979-local-fields`. Worker 96 read V.3, printed pp.83–85 / PDF pp.90–92
and the registered 2019 author corrections, PDF pp.2–3; no correction affects
that passage. The implementation proves only the support results described
above. Trace terms and their nonvanishing, the norm-expansion remainder, and
the complete graded-norm formulas remain separate obligations.
