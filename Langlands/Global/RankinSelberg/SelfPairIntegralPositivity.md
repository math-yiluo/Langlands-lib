# Positive global and finite partial self-pair integrals

Internal positivity helpers for the proof of `CuspidalSelfPairContinuationStatement`.

At a real parameter where it is integrable, the Whittaker integrand for a vector
and its conjugate has real part
`norm(W(g))^2 * Phi(lastRow(g)) * exp(sigma * log(detNorm(g)))`.
Assume that the real test function is nonnegative and Schwartz--Bruhat, and is
positive at the last row of a point where `W` is nonzero. Then this real part is
nonnegative everywhere and positive at the class of that point.

The actual quotient integrand is continuous: pull it back to the adelic group by
the quotient map, use the representative-independent formula, and combine
continuity of cusp Whittaker functions, of the Schwartz--Bruhat test, of the last
row and of the determinant power. Full support of the fixed quotient measure,
proved in `SelfPairPositiveData`, and Mathlib's positive-integral theorem give a
strictly positive global integral.

The partial integration domains `unipotentIntegralClasses` increase to the whole
quotient, as proved in the module `PartialIntegralExhaustion`. For an
integrable real function with positive total integral, their integrals converge
to that positive number. Thus a sufficiently large finite domain has positive
integral and can also contain any prescribed finite set. Applying this to the
real part of the self-pair integrand gives a positive finite partial integral.

This is an internal argument from the Library integral definitions and measure
properties. It assumes integrability at the selected real parameter explicitly;
it does not assert equal-rank unfolding or continuation of an Euler product.

`SelfPairIntegralPositivityStatement` records these two positivity conclusions
with all the stated hypotheses, including integrability. It retains the chosen
real parameter and allows the resulting partial domain to contain an arbitrary
prescribed finite set. `selfPairIntegralPositivity` proves it.
