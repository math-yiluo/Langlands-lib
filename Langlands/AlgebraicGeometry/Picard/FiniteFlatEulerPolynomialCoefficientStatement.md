# Native finite-flat rank in top Euler polynomial coefficients

`FiniteFlatEulerPolynomialCoefficientStatement` concerns an actual finite flat
scheme morphism `f : X ⟶ Y` over an arbitrary field. The target `Y` is integral,
Noetherian, separated and proper over the field, with topological Krull dimension
at most a specified natural number `d`. For an actual line bundle `L` on `Y`, it
assumes finite cohomology of all tensor powers of `L` and of its actual pullback.
For any rational polynomials representing those two actual Euler sequences at
every natural argument, it asserts
`Q.coeff d = (f.finrank x : ℚ) * P.coeff d` at each target point `x`.

No degree bound, nonzero polynomial, ampleness, positive rank, or positive
dimension is assumed. In particular `d = 0` and rank zero are included. This is
a coefficient statement at the dimension bound; it does not assert a
leading-coefficient identity when the actual degree is smaller, nor does it
supply the polynomial representatives as part of its conclusion.

This is internal derived content from the actual sheaf and Euler comparisons.
The finite-flat pushforward of the source structure module has finite affine
sections and is quasi-coherent. Its published generic-basis theorem supplies a
nonempty affine open where it is free with basis cardinality equal to the native
rank at `x`. A global free sheaf of that cardinality has the same restriction
there. The coherent support-dimension comparison makes the difference of their
Euler sequences vanish after `d` forward differences. Finite-free additivity
identifies the free coefficient with the native rank multiple of the original
line-bundle Euler sequence. The affine projection comparison identifies the
pushforward coefficient with the actual pulled-back Euler sequence. Finally,
Newton reconstruction makes the coefficient in degree `d` of their polynomial
difference zero. Thus the native rank arises from the actual finite-flat
pushforward; no rank formula or numerical certificate is assumed.
