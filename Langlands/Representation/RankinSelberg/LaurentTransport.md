# Laurent monomial transport of continuations and zeta modules

This is an internal algebraic bridge for transport of the local spectral
variable `X = q^(-s)`. It imports the published `LocalFactor` module, hence the
actual Laurent coefficient ring and its embedding from `RationalZeta`, and the
right-half-plane continuation relation from `RationalContinuation`. It adds no
new factor predicate and assumes no analytic existence theorem.

## The invertible scalar

For `c : ℂˣ` and `m : ℤ`, `laurentMonomialUnit c m` is the unit of
`LaurentCoefficients = LaurentPolynomial ℂ` whose value is

`LaurentPolynomial.C (c : ℂ) * LaurentPolynomial.T m`.

Its inverse is explicitly `C(c⁻¹) T(-m)`. Both inverse identities follow from
multiplicativity of the constant embedding and `T(m) T(-m) = T(0) = 1`.
`laurentToRatFunc_monomialUnit` identifies its image in the published rational
function field as `RatFunc.C c * RatFunc.X ^ m`.
`laurentMonomialUnit_inv` identifies the inverse unit with the same construction
at `(c⁻¹, -m)`.

## Generated modules

`zetaSpan_eq_of_unit_mul` applies to arbitrary sets `S` and `T` of rational
functions and an actual unit `u` of the Laurent coefficient ring. Its two
hypotheses are

* for every `R ∈ S`, the embedded scalar `u` times `R` belongs to `T`;
* for every `R ∈ T`, the embedded scalar `u⁻¹` times `R` belongs to `S`.

It proves `zetaSpan S = zetaSpan T`. For the first inclusion, each transported
generator belongs to the target span. Multiplication by `u⁻¹`, an allowed
Laurent scalar, recovers the original generator. The second inclusion uses the
same argument with the inverse unit. The sets themselves need not be equal.

`zetaSpan_eq_of_monomial_mul` specializes this result to the two reciprocal
scalars `c X^m` and `c⁻¹ X^(-m)`. The coefficient is a unit; a zero coefficient
would not justify this conclusion. Applying the already published
`isNormalizedGenerator_congr` or `normalizedGeneratorExists_congr` to the
result transfers the normalized-generator relation or its existence. This
module does not assert that either relation holds for any particular integral
family.

## Rational continuations

The imported `HasRationalContinuation q f R` requires an actual right
half-plane on which the reduced denominator of `R` never vanishes and
`f(s) = R(q^(-s))`. Its pole-exclusion condition is preserved explicitly.

`HasRationalContinuation.mul` combines two continuations by taking the larger
of their half-plane bounds. The reduced denominator of a product divides the
product of the two reduced denominators, so it remains nonzero on that
half-plane. Mathlib's `RatFunc.eval_mul` then supplies the evaluation identity.
`HasRationalContinuation.pow` follows by induction on a natural exponent;
its exponent-zero case is the constant rational function one.

`hasRationalContinuation_spectralPoint q` identifies the continuation of
`q^(-s)` with `X` for every natural `q`. The integer-power version,
`hasRationalContinuation_spectralPoint_zpow hq m`, requires `hq : 0 < q`.
This ensures that `q^(-s)` is never zero for any complex `s`. For the inverse
power, the denominator of `X⁻¹` divides the numerator `X`; its evaluation is
therefore nonzero. Evaluation of `X * X⁻¹ = 1` then identifies evaluation of
`X⁻¹` with `(q^(-s))⁻¹`. Natural powers of these two base continuations cover
positive and negative integer exponents. These arguments also allow `q = 1`;
uniqueness of general continuations, which requires `q > 1` in the published
API, is neither used nor claimed here.

Finally, `HasRationalContinuation.monomial_mul hq h c m` takes a continuation
`h` of `f` by `R` to a continuation of

`fun s => c * spectralPoint q s ^ m * f s`

by `RatFunc.C c * RatFunc.X ^ m * R`. Here `c : ℂ` may be zero: this lemma is
only forward transport of a continuation. It uses the integer-power result,
the product result and the published `hasRationalContinuation_const_mul`.
The stronger nonzero coefficient requirement appears in the span theorem,
where invertibility is essential.

## Provenance and boundaries

The construction is derived directly from the published project definitions
and Mathlib's Laurent polynomial, rational function, unit and submodule APIs;
no independent literature claim is introduced. The implemented proof route is
the algebraic argument above. The intended consumer is character-change
transport, where an independently proved integral identity must identify its
scalar with a Laurent monomial and must transport the actual generating data.
No determinant weight identity, Haar modulus law, convergence of an integral,
existence of a rational continuation, or character independence of an L-factor
is asserted in this unit.
