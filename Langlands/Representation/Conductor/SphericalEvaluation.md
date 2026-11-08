# Evaluation of finite spherical Laurent numerators

This internal algebraic unit evaluates the rational Laurent numerators constructed
in `SphericalRational`. It proves that these rational functions have no pole at a
nonzero scalar and that their rational evaluation equals the corresponding
finite Laurent sum. For homogeneous coefficients this is evaluation of the
finite coefficient sum after scaling the tuple. The final application constructs
the symmetric Laurent numerator of the actual spherical model product.

## Denominators and integer powers

All scalar evaluation lemmas use an arbitrary field `K`, the identity coefficient
homomorphism `RingHom.id K`, and a scalar `c : K`. Reduced rational-function
denominators are the denominators used by `RatFunc.eval`.

The private denominator lemmas use the following facts. If a denominator divides
a polynomial that evaluates nonzero, the denominator also evaluates nonzero.
The reduced denominators of a sum or product divide the product of the original
denominators. Thus nonvanishing at `c` is preserved by sums, products and finite
sums. Finite induction, together with `RatFunc.eval_add`, then proves additivity
of evaluation on a finite collection with nonvanishing denominators.

For `c ≠ 0` and every integer `d`, `rationalXPow_denom_eval_ne_zero` proves that
the denominator of `RatFunc.X ^ d` evaluates nonzero at `c`. A nonnegative power
is the image of a polynomial and has denominator one. For a negative exponent,
the rational function is the inverse of a nonzero polynomial power; its reduced
denominator divides the polynomial `X^(n+1)`, which evaluates to the nonzero
scalar `c^(n+1)`.

`rationalXPow_eval` proves that evaluation of `RatFunc.X ^ d` at `c` is `c^d`.
For a nonnegative exponent it uses polynomial evaluation. For a negative
exponent it evaluates the product of the positive power and its inverse; both
denominators have already been shown nonvanishing. The product evaluates to
one, so the inverse evaluates to the inverse of the positive scalar power.

`rationalMonomial_denom_eval_ne_zero` and `rationalMonomial_eval` apply these
results to `RatFunc.C a * RatFunc.X ^ d`. Its denominator is nonzero at `c`, and
its evaluation is `a * c^d`. Here `a` may be zero.

## A finite rational Laurent sum

Let `A` be any commutative ring, `S : LaurentSeries A`,
`hS : S.support.Finite`, and `f : A →+* K`. The imported construction
`finiteLaurentRationalFunction S hS f` is the actual finite sum of the monomials
`C (f (S.coeff d)) * X^d`, with `d` in `hS.toFinset`.

`finiteLaurentRationalFunction_denom_eval_ne_zero` proves that its denominator
evaluates nonzero at every nonzero scalar `c`. This also covers the zero series
and specializations where original nonzero coefficients become zero.

`finiteLaurentRationalFunction_eval` proves

```text
RatFunc.eval (RingHom.id K) c (finiteLaurentRationalFunction S hS f)
  = sum over d in hS.toFinset of f (S.coeff d) * c^d,
```

provided `c ≠ 0`. The proof uses the finite-sum evaluation lemma and the
monomial formula, with the proved denominator nonvanishing at every step.
`finiteLaurentRationalFunction_eval_one` specializes this identity to `c = 1`:
it equals `f (finiteLaurentCoefficientSum S hS)`.

## Homogeneous scaling

Let `σ` be any finite coordinate type and let
`S : LaurentSeries (symmetricTorusSubalgebra σ K)` have finite support, with
`S.coeff d` homogeneous of integer degree `d` for every `d`. For a unit tuple
`x : σ → Kˣ` and a unit `c : Kˣ`,
`finiteLaurentRationalFunction_eval_eq_symmetricTorusEvaluation_scale` proves

```text
RatFunc.eval (RingHom.id K) (c : K)
  (finiteLaurentRationalFunction S hS (symmetricTorusEvaluation σ K x))
  = symmetricTorusEvaluation σ K (fun i => c * x i)
      (finiteLaurentCoefficientSum S hS).
```

The coefficient map in the actual Lean expression is the evaluation algebra
homomorphism's underlying ring homomorphism. The proof compares the finite
rational evaluation formula with
`symmetricTorusEvaluation_finiteLaurentCoefficientSum_scale` from
`SphericalProduct`. Scalar commutativity matches the order of the factors. No
infinite series or analytic limit is evaluated, and the scalar field need not
be infinite or algebraically closed for this result.

## The actual symmetric model numerator

The model application retains the hypotheses of `SphericalRational`: an
arbitrary nonarchimedean local field `F`, the measurable and Borel instances in
the Lean signature, a Jacquet normalization `h`, a smooth complex representation
`π` of `GL_(n+2)(F)`, a Whittaker functional `ℓ`, an actual vector `w` in its
coefficient model, and a scalar polynomial `P`. The field and representation
universes remain independent.

Given an explicit proof

```text
hfinite : (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite,
```

`corankOneModelNumerator h π hπ ℓ w P hfinite` is the finite sum of the actual
coefficients of that product. Its value belongs to the symmetric Laurent
coefficient algebra `symmetricTorusSubalgebra (Fin (n+1)) ℂ`.

`corankOneModelNumerator_evaluation` expresses its value at a unit tuple `x` as
the finite sum of the product's specialized coefficients. Thus this numerator
uses the actual integrated coefficients and their finite polynomial
convolutions already constructed in the preceding modules.

`corankOneModelRationalNumerator_denom_eval_ne_zero` proves that the existing
scalar rational numerator at `x` has no pole at any nonzero complex scalar.
`corankOneModelRationalNumerator_eval` proves that its value at `c : ℂˣ` equals
the value of `corankOneModelNumerator` at `fun i => c * x i`. This uses the proved
homogeneity of every actual model-product coefficient.
`corankOneModelRationalNumerator_eval_one` gives its value at one as evaluation
of the symmetric numerator at the original tuple `x`.

## Provenance and scope

These are internal algebraic consequences of the actual constructions in
`SphericalProduct` and `SphericalRational`, with Mathlib's reduced denominator
and rational evaluation identities. No additional literature assertion is a
premise. The implemented route explicitly proves denominator nonvanishing
before applying additivity or multiplicativity of rational evaluation.

The unit does not establish the finite-support hypothesis, analytic convergence,
rational continuation of the actual integral, an L-polynomial or its existence,
the functional equation, absence of common zeros for a numerator ideal, an
essential vector, uniqueness, or a conductor theorem. Those remain obligations
for the corrected essential-vector argument and the exact task target.
