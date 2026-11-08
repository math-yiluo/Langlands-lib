# Rational functions from finite spherical Laurent products

This internal algebraic bridge constructs a rational Laurent numerator from the
actual finite-support denominator product in `SphericalProduct`. It proves that
the actual scalar model series is the formal Laurent expansion of that numerator
times the existing `essentialFactor`. Finiteness of the product's actual support
and normalization of the scalar polynomial are explicit hypotheses.

## Canonical polynomial embedding

For every commutative ring `A`,
`finitePolynomialLaurentSeries_eq_algebraMap` identifies the finite-sum
construction in `SphericalDenominator` with
`algebraMap (Polynomial A) (LaurentSeries A)`. The proof compares coefficients
through the canonical polynomial-to-power-series and power-series-to-Hahn-series
maps. Both embeddings have coefficient `P.coeff m` at a nonnegative exponent
`m` and zero at a negative exponent.

`finitePolynomialLaurentSeries_ne_zero` then follows from injectivity of the
canonical polynomial embedding. It needs no field hypothesis.

## A rational function from finite Laurent support

Let `A` be a commutative ring, `K` a field, `S : LaurentSeries A`, and
`hS : S.support.Finite`. For a ring homomorphism `f : A →+* K`,
`finiteLaurentRationalFunction S hS f` is the actual rational function

```text
sum over d in S.support:
  RatFunc.C (f (S.coeff d)) * RatFunc.X^d.
```

The sum runs over the finite set obtained from the supplied proof of finiteness.
The exponents are integers, so this construction allows negative exponents.
There is no evaluation of an infinite series.

`rationalMonomial_laurentExpansion` proves that the canonical expansion of
`C a * X^d` in `LaurentSeries K` is `HahnSeries.single d a`. The proof uses
compatibility of the polynomial and rational-function algebra maps, preservation
of integer powers by a field homomorphism, and the integer-power formula for
Hahn monomials.

`finiteLaurentRationalFunction_laurentExpansion` proves

```text
algebraMap (RatFunc K) (LaurentSeries K)
  (finiteLaurentRationalFunction S hS f) = S.map f.
```

It maps the finite sum into Laurent series and compares coefficients. For a
fixed exponent, at most the monomial with that exponent contributes. If the
exponent lies outside the original support, its original coefficient is zero,
and so is its image under `f`.

## The existing essential factor

For `P : Polynomial ℂ` and `x : Fin m → ℂˣ`, write

```text
D_x = product_i P.comp (C (x_i) * X).
```

`specializedCoordinateDenominator_coeff_zero` proves that `D_x.coeff 0 = 1`
whenever `P.coeff 0 = 1`, by evaluating the product at zero. Consequently
`specializedCoordinateDenominator_ne_zero` proves `D_x ≠ 0`, also for rank zero
where the product is empty.

The imported `essentialFactor P x` is the reciprocal of the polynomial `D_x`
in `RationalFunctions = RatFunc ℂ`.
`essentialFactor_laurentExpansion` proves that its canonical formal Laurent
expansion is `(finitePolynomialLaurentSeries D_x)⁻¹`. This equality holds for
every `P`, using totalized field inversion. Under the additional normalization
`P.coeff 0 = 1`,
`essentialFactor_laurentExpansion_mul_denominator` proves that the expansion
times the finite denominator series equals one. This cancellation uses the
proved nonvanishing, rather than an assumption about a totalized inverse.

## The numerator of the actual model series

Here `F` is any nonarchimedean local field, with the measurable and Borel
instances in the Lean signature. The data are an actual Jacquet normalization
`h`, a smooth complex representation `π` of `GL_(n+2)(F)`, a Whittaker functional
`ℓ`, a vector `w` in its coefficient model, and a scalar polynomial `P`. The
field and representation universes are independent.

Given

```text
hfinite :
  (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite,
```

`corankOneModelRationalNumerator h π hπ ℓ w P hfinite x` applies
`finiteLaurentRationalFunction` to this actual denominator product and the
coefficient homomorphism `symmetricTorusEvaluation ... x`. Thus it uses the
actual integrated model coefficients through their finite convolutions.

`corankOneModelRationalNumerator_laurentExpansion` identifies its expansion with

```text
specializedCorankOneModelLaurentSeries h π hπ ℓ w x
  * finitePolynomialLaurentSeries D_x.
```

The proof combines the finite-support expansion theorem with the exact
specialization identity in `SphericalProduct`.

Finally, if `P.coeff 0 = 1`,
`specializedCorankOneModelLaurentSeries_eq_laurentExpansion` proves

```text
specializedCorankOneModelLaurentSeries h π hπ ℓ w x
  = algebraMap RationalFunctions (LaurentSeries ℂ)
      (corankOneModelRationalNumerator h π hπ ℓ w P hfinite x
        * essentialFactor P x).
```

This is a formal rational expression for the actual scalar degree-integral
series. Its proof multiplies the numerator expansion by the expanded essential
factor and cancels the nonzero coordinate denominator.

## Provenance and remaining obligations

These are internal algebraic deductions from the preceding actual model-series,
coordinate-denominator, and finite-support constructions and Mathlib's canonical
embeddings. Their role is to connect the finite Laurent numerator in the
corrected essential-vector argument with the existing rational-function
interface. No separate literature assertion is used as a proof premise.

The unit does not prove that the denominator product has finite support; a
uniform upper bound from a functional equation is still needed. It also does
not prove that `P` is an L-polynomial, that an L-polynomial exists, that the
numerator equals one for an essential vector, analytic convergence, rational
continuation of the actual integral, uniqueness, or a conductor theorem.
