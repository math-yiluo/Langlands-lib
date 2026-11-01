# Shifted rational equations on Fourier-regular matrix tests

This internal construction converts the actual unshifted operator equation
on Fourier-regular tests into the normalized equation for actual rational
values. Its provenance is the existing compact-support Laurent integral
formula, rational-continuation uniqueness, evaluation of the actual zeta
operators, and the existing reflected rational form of a monomial functional
equation. It introduces no new rational-existence or supercuspidality premise.

For the canonical p-adic field and matrix size `d=n+1`, the normalized
integral uses exponent `s+t`, where `t=jpssShift n=n/2`. The definition
`shiftedMatrixMonomialUnit F n c k` is the complex unit
`c * spectralShiftUnit(q,t)^k`. Its monomial at parameter `s` equals the
original monomial `c * spectralPoint(q,s+t)^k`. Thus the scalar correction
depends only on the field, rank and original unit and integer, and is fixed
before any test, vector or functional.

`regularMatrixRationalValue_eval` takes a regular full-matrix test, a continuous
coefficient and any supplied actual shifted rational value `R`. Restriction
of the test to GL has compact support, so its product with the coefficient
has compact support. The existing Laurent integral formula gives absolute
convergence and a Laurent evaluation at every complex parameter. That Laurent
polynomial supplies a guarded continuation on a right half-plane. Uniqueness
for `q>1` identifies it with `R`. Consequently `R` is regular at every nonzero
spectral point and its evaluation is the actual integral at every parameter.
No equality between a left and a right convergence half-plane is assumed.

`normalizedFunctionalEquation_of_fourierRegular_operator` assumes smoothness
of the representation and its literal inverse-transpose pullback, and the
unshifted operator equation for one Fourier-regular test at every complex
parameter with a fixed unit `c` and integer `k`. For any vector, algebraic
functional and supplied actual original and dual rational values, it proves
`NormalizedFunctionalEquation q 1 1 1 cShift 0 k R RDual`. The two tests are
regular, and smooth orbit maps make both coefficient functions continuous,
so the evaluation lemma applies at `s` and `1-s`. Evaluating the assumed
operator equation at `s+t` gives the result because
`d-(s+t)=(1-s)+t`. The equation retains both published denominator guards.

`matrixRationalPairing_identity_of_fourierRegular_operator` applies this
result to the chosen actual pairings from `ContinuedMatrixCovariance`, whose
universal rational-existence premises remain explicit. The existing theorem
`NormalizedFunctionalEquation.rational_identity` gives the equality in the
complex rational-function field:

```text
subst(q⁻¹, dualPairing(Phi,v))
  = laurentToRatFunc(monomial(cShift,k)) * originalPairing(Phi,v).
```

Here substitution is exactly `X ↦ q⁻¹/X`, the dual coefficient is literal
inverse-transpose precomposition, and the dual test is the full plus Fourier
transform for the supplied self-dual scalar measure and its exact square
product. The field and representation carrier have independent universes.
The statements remain restricted to Fourier-regular tests; extension to
arbitrary full-matrix tests is a separate obligation.
