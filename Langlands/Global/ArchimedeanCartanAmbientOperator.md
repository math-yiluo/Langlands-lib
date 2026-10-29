# Ambient matrix realization of genuine Cartan polynomial actions

This internal construction realizes the genuine action of the Cartan
square sum, of its powers and of complex polynomials in it as one
concrete expression on functions on the ambient real matrix space. It
imports the published `ArchimedeanCartanSymbol` module and, through it,
the normalized Cartan basis of `ArchimedeanCasimirCartan`, the genuine
differentiation of `ArchimedeanSmoothDifferential` and the genuine
enveloping action of `ArchimedeanEnvelopingAction`. None of those modules
is changed. Worker 94 wrote the development; Worker 880 checked it
against the published prerequisites and added the documentation of the
coordinate-extension specializations and the constant-polynomial
corollary.

Every declaration is stated for an arbitrary number field `K : Type u`
and every natural rank `n`, including `n = 0`. The carrier is the
original real matrix space `ArchimedeanMatrix K n`, with its published
matrix operator norm and topology. Functions take complex values.

## The ambient operator

`cartanAmbientOperator F` is defined for every function
`F : ArchimedeanMatrix K n → ℂ`. Write `Xᵢ` for the matrix
`realLieAlgebraToMatrix K n (cartanAdaptedBasis K n i)`. The index runs
over the whole published normalized Cartan basis. At every ambient
matrix `y`, invertible or not, the value is

```text
Σᵢ (D²F(y)(y * Xᵢ)(y * Xᵢ) + DF(y)(y * (Xᵢ * Xᵢ))).
```

Here `DF(y)` is `fderiv ℝ F y` and `D²F(y)` is
`fderiv ℝ (fderiv ℝ F) y`. These are Mathlib's real Frechet derivatives,
which are defined for every function. The second summand is the
first-order moving-frame correction. It is kept for every basis index.

## Polynomial expressions

`cartanAmbientPolynomial p F` is defined for every complex polynomial
`p` by `p.sum fun m c => c • (cartanAmbientOperator K n)^[m] F`. This is
the finite sum, over the support of `p`, of each coefficient times the
corresponding iterate of the operator applied to `F`. The zeroth iterate
is the identity. The zero polynomial gives the empty sum. The definition
is a concrete expression. It does not postulate an algebra homomorphism
on arbitrary ambient functions.

## Identities on units

The comparison theorems use one premise on `F`. For a genuine smooth
function `f : SmoothFunctions K n`, the premise says that
`F g = f.val ((archimedeanGLCoordinates K n).symm g)` for every actual
unit `g`. This is a coordinate realization premise only. The theorems
assume no smoothness, analyticity or other regularity of `F` away from
the units. All conclusions are values at actual units `g`.

`cartanAmbientOperator_eq_of_extension` proves that
`cartanAmbientOperator F g` equals the value of
`envelopingAction K n (cartanSquareSum K n) f` at
`(archimedeanGLCoordinates K n).symm g`. The units form an open set,
so `F` agrees with `coordinateExtension K n f` on a neighborhood of
`g`. This eventual equality identifies the first Frechet derivatives at
`g`. Applied to the first derivatives, it also identifies the second
Frechet derivatives at `g`. The operator applied to `F` therefore equals
the operator applied to `coordinateExtension K n f` at `g`. The published
theorem `envelopingAction_cartanSquareSum_apply` gives exactly this
formula for the genuine action, with every first-order correction.

`cartanAmbientOperator_iterate_eq_of_extension` proves the corresponding
identity for every natural iterate `m` and the genuine action of
`cartanSquareSum K n ^ m`. The proof is by induction on `m`. For `m = 0`
it is the premise together with `envelopingAction_one`. For the
successor, the induction hypothesis says that the previous iterate
agrees on units with the genuine smooth function
`envelopingAction K n (cartanSquareSum K n ^ m) f`. The one-operator
theorem then applies to the previous iterate itself. The action's
multiplication law `envelopingAction_mul` identifies the result with
the action of the next power. The whole previous ambient expression is
differentiated by the next application; no term is dropped.

`cartanAmbientPolynomial_eq_of_extension` proves that
`cartanAmbientPolynomial p F g` equals the value of
`envelopingAction K n (Polynomial.aeval (cartanSquareSum K n) p) f` at
`(archimedeanGLCoordinates K n).symm g`, for every `p : Polynomial ℂ`.
The genuine action is a complex algebra homomorphism, so
`Polynomial.aeval_algHom_apply` moves it inside the polynomial
evaluation. `Polynomial.aeval_endomorphism` writes the resulting
endomorphism as the coefficient sum of its powers. Each summand is then
the iterate identity.

## Coordinate-extension specializations

`cartanAmbientOperator_coordinateExtension`,
`cartanAmbientOperator_iterate_coordinateExtension` and
`cartanAmbientPolynomial_coordinateExtension` take
`F = coordinateExtension K n f`. The published theorem
`coordinateExtension_apply` supplies the premise. The iterate theorem
includes `m = 0`. The polynomial theorem includes the zero polynomial
and every constant polynomial. At the end of the Lean file, one
`example` checks the complete unapplied type of
`cartanAmbientPolynomial_eq_of_extension`, and two more display the
cases `m = 0` and `p = 0`.

`cartanAmbientPolynomial_C_coordinateExtension` evaluates the constant
case. For `c : ℂ`, the expression for `Polynomial.C c` equals
`c * f.val ((archimedeanGLCoordinates K n).symm g)` at every unit `g`.
It follows from the polynomial specialization, `Polynomial.aeval_C`,
the algebra-map law of the genuine action and the scalar action on
endomorphisms.

## Provenance and scope

The provenance is internal. The construction uses the Frechet
derivative, openness of the units, the published second-order formula,
the algebra laws of the genuine enveloping action and Mathlib's
polynomial evaluation. It introduces no norm, topology, symbol
certificate, rank restriction, regularity assumption or axiom.

These identities realize powers and polynomial actions as iterates of a
single ambient expression. They do not identify the highest-order
coefficient of an iterate with a power of the quadratic symbol, and
they construct no general algebra of differential operators. Analytic
coefficient estimates, analytic elliptic regularity, analyticity of
solutions, Lie-orbit density, admissibility, reproduction and final
automorphic differential growth remain separate obligations.
