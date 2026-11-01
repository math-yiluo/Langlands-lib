# Signed functional equation for the adjacent finite products

This derived prerequisite combines the supplied equal-rank and matrix
normalized functional equations into the functional equation of the
literal original and model-star finite products. It implements the
comparison of JPSS Section 6.3 formulas (12), (13) and (14), printed
pp.436–438, with the actual reflected-test scalar proved separately.

`absorbedFunctionalEquationSign zeta c e` is the actual unit
`zeta^e*c`. The sign-absorption theorem proves equivalence between a
normalized functional equation with explicit model scalar `zeta` and
sign exponent `e`, and one with trivial model scalar, sign exponent zero,
and this absorbed epsilon unit. The polynomials, rational functions,
Laurent exponent and both denominator guards remain identical. The
proof unfolds the actual epsilon monomial and reassociates its factors.

`normalizedFunctionalEquation_mul_dual_sign` proves that multiplying the
dual rational value by `RatFunc.C(zeta)` increases the recorded sign
exponent from `e` to `e+1`. The nonzero constant is a unit. A denominator
guard for the scaled dual value implies the guard for the original
value: multiply the scaled value by `C(zeta^-1)`, use the existing
product-denominator nonvanishing lemma, and cancel the constant.
The rational evaluation law then identifies its evaluation as the
constant multiple. Applying the original functional equation and
`pow_succ` gives the increased sign. Thus no original pole guard is
silently dropped.

Suppose the supplied quotient value pairs `A_i,AD_i` satisfy
`NormalizedFunctionalEquation` with polynomials `P0,PD0`, model scalar
`zeta`, sign exponent `r`, epsilon unit `c0` and Laurent exponent `m0`.
Suppose the supplied matrix value pairs `M_i,MD_i` satisfy it with
polynomials `P1,PD1`, trivial model scalar, sign exponent zero, epsilon
unit `c1` and Laurent exponent `m1`.
`normalizedFunctionalEquation_adjacent_sum_mul` proves that

```text
R  = sum_i A_i * M_i,
RD = C(zeta) * sum_i AD_i * MD_i
```

satisfy the normalized equation with product polynomials
`P0*P1,PD0*PD1`, model scalar `zeta`, epsilon unit `c0*c1`,
Laurent exponent `m0+m1`, and exactly sign exponent `r+1`.
The finite index set is arbitrary, including empty.

The proof absorbs the quotient sign into `c0`, applies the existing
`GodementJacquet.normalizedFunctionalEquation_sum_mul`, restores the
quotient sign, then uses the dual-scaling theorem. The existing
finite-sum theorem uses its established limiting argument at canceled
summand poles; it requires only the two guards for the resulting sums.
Reusing it avoids assuming that all summand denominators are nonzero
where the finite sum is regular.

For the canonical p-adic field,
`adjacentRank_reflectedFiniteProducts_functionalEquation` applies this
calculation to the literal dual product expression

```text
C(modelStarScalar) *
  sum_i AD_i * (C(dualMatrixReflectionScalar) * MD_i).
```

The already proved exact sign cancellation identifies this expression
with `C(zeta)*sum_i AD_i*MD_i`. The canonical residue cardinality is
greater than one, so the supplied finite-sum functional-equation theorem
applies. With inner group rank `r+1` and ambient group rank `r+2`, the
equal-rank sign exponent is `r`, and the required ambient unequal-rank
sign exponent is `r+1`, exactly as in the conclusion. All polynomial,
unit, Laurent-exponent, finite-family and denominator data are retained.

The source is Jacquet–Piatetski-Shapiro–Shalika, *Rankin–Selberg
Convolutions* (1983), registered as `jpss-1983-rankin-selberg`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pp.404–405 and 427–439 were read in preceding work; pp.435–437
were visually reread for the finite-product and reflected-test
calculations. The comparison after (14) uses the two earlier normalized
functional equations and the extra model-minus-one scalar from
reflection. The implemented sign absorption is an internal algebraic
route to that comparison. The earlier bounded registered-source and
correction-note audit found no JPSS-specific registered erratum.

These are algebraic assembly theorems for supplied functional equations
and rational values. They do not assert existence of the matrix
functional-equation data, polynomial certificates, matrix analytic
witnesses or ambient model realization. Applying them to the actual
matched product continuations, full-type factor certification,
normalized lower-to-upper transport and both parent gamma/L
statements remain separate obligations.
