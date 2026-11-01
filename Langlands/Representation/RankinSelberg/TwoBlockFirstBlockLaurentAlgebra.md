# Finite Laurent algebra for the first-block calculation

Author: Worker 1191.

This module supplies derived algebraic helpers for the polynomial-cleared
first-block identity. It imports the published bilateral Laurent module,
`EpsilonFactor` and `EqualRankSwapTransport`. Every series is an arbitrary
function `Z : ℤ → ℂ`; no support bound is assumed.

The source motivation is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin-Selberg convolutions* (1983), Section 4.1, printed page 406, and
Section 4.9, printed pages 416–418, registered as
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
These helpers are derived formal packaging of finite polynomial actions and
scalar comparisons, rather than definitions quoted from the article. Their
proofs use the imported Lean results and elementary finite-sum algebra.

All declarations below lie in
`Langlands.RankinSelberg.TwoBlockFirstBlockLaurent`.

## Exact polynomial actions

`reflectedPolynomial q P` is the Laurent polynomial

```text
Polynomial.eval₂ LaurentPolynomial.C
  (LaurentPolynomial.C ((q : ℂ)⁻¹) * LaurentPolynomial.T (-1)) P.
```

Thus it is exactly `P(q⁻¹ X⁻¹)`, including the zero polynomial. Its definition
makes sense for every natural `q`; no nonzero-cardinality assumption is
needed for these finite algebraic identities.

`toLaurent_eq_sum` and `reflectedPolynomial_eq_sum` give the finite Laurent
monomial expansions, using the natural-number support of `P`. The former
maps the polynomial's sum of monomials through `Polynomial.toLaurent`. The
latter expands polynomial evaluation and uses multiplication and powers of
Laurent monomials. Applying the published monomial action gives
`toLaurent_smul_apply` and `reflectedPolynomial_smul_apply`:

```text
(P.toLaurent • Z) k
  = ∑ i ∈ P.support, P.coeff i * Z(k-i),
(reflectedPolynomial q P • Z) k
  = ∑ i ∈ P.support, (P.coeff i * ((q : ℂ)⁻¹)^i) * Z(k+i).
```

`epsilonPolynomial_smul_apply` gives

```text
((C c * T d * P.toLaurent) • Z) k
  = c * ∑ i ∈ P.support, P.coeff i * Z(k-d-i).
```

Here natural support indices are cast to integers in every coefficient
argument. `identity_iff_coefficients` states that the desired reflected
polynomial action equality, for arbitrary supplied `q,P,Pdual,c,d,Zup,Zlow`,
is equivalent to equality of these two finite sums at every integer `k`.
The proof uses extensionality of coefficient functions. It does not cancel
any polynomial on the bilateral module, which has torsion.

## Coefficientwise integration and the cube scalar

For any measurable space `A`, measure `μ` and coefficientwise integrable
family `S : A → BilateralLaurentSeries`,
`reflectedPolynomial_integral_apply` integrates the displayed finite
reflected coefficient sum and identifies the result with the action on
`coeffwiseIntegral μ S`. This follows from the published
`coeffwiseIntegral_laurent_smul` and the coefficient formula above.

`integral_laurent_identity` takes two coefficientwise integrable families
`S,U`, fixed Laurent polynomials `D,Q`, and a pointwise equality
`D • S x = Q • U x`. It integrates to

```text
D • coeffwiseIntegral μ S = Q • coeffwiseIntegral μ U.
```

The same polynomials are retained. The proof commutes each fixed finite
Laurent action with coefficientwise integration, then uses the pointwise
identity. It asserts no integrability of an actual JPSS quotient function;
that analytic input must be supplied by the caller.

`cube_mass_cancel` is an elementary scalar comparison: for a nonzero real
`c`, if `Zup = c • Zmixed` and `Zradical = c • Zmixed`, it proves both
`Zup = Zradical` and `c⁻¹ • Zup = Zmixed`. In the intended application `c`
is the positive finite rectangle-cube mass converted to a real number.
The lemma itself has no measure hypotheses and does not establish either
geometric comparison. The reciprocal assertion follows from scalar
associativity and `c⁻¹*c=1`.

## Actual minus-one scalar and orientation

`normalizedGenerator_functionals_ne_zero` works over a general field `F`
with a topology, arbitrary measurable spaces on the small quotient and
rectangle, and independent universes for `F`, `V` and `W`. For an actual
fixed-block value set `unequalRankValuesAt j k hr q ψ abv μ ρ π σ ℓ ℓ'`, a
supplied `IsNormalizedGenerator` and `1 < q` force both underlying supplied
linear functionals to be nonzero. No irreducibility or nonzero-functional
assumption is added.

The proof extracts a nonzero rational value using the published
`IsNormalizedGenerator.exists_ne_zero`. Its actual coefficient pair cannot
have a zero coefficient function: that would make the unequal-rank integral
the zero function, and uniqueness of rational continuation for `q > 1`
would make the rational value zero. Surjectivity of each actual coefficient
model map then excludes zero supplied functionals. The rank equality is
eliminated before this reasoning, preserving the actual transported value
set and arbitrary supplied rectangle measure.

`minusOneScalar_sq_eq_one` combines the resulting nonzero second functional
with the actual certificate `HasModelMinusOneScalar σ ℓ' ζ`. The imported
`HasModelMinusOneScalar.sq_eq_one` applies the action of `-I` twice to a
nonzero coefficient value and proves `ζ²=1`. This is a consequence inside
the normalized-generator clause; it imposes no restriction on zero
functionals in an unconditional convergence statement.

For any unit `ζ` with `ζ²=1`, `scalar_pow_mul_self` proves
`(ζ : ℂ)^t * (ζ : ℂ)^t = 1` for every natural `t`.
`orient_laurent_identity` uses this to transform

```text
(C c * T d * P.toLaurent) • Zup = (C ((ζ : ℂ)^t) * D) • Zlow
```

into

```text
D • Zlow = (C ((ζ : ℂ)^t * c) * T d * P.toLaurent) • Zup.
```

It multiplies the equality by the complex scalar `(ζ : ℂ)^t`, uses the
constant Laurent action and scalar associativity, and removes the resulting
unit scalar of value one. The exact polynomials remain unchanged.

This module proves no analytic first-block comparison, row Fourier identity,
convergence bound, normalized-generator existence, or epsilon-certificate
existence. It changes none of the target statement's imported files.
