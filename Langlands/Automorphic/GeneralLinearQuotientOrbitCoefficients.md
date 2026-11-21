# Scalar orbit coefficients of stable form classes on the positive quotient

`Langlands.Automorphic.GroupSchemeFunctions.GeneralLinearQuotientOrbitCoefficientsStatement`
and its proof `generalLinearQuotientOrbitCoefficients` concern the original
positive-central rational quotient of `GL_{r+1}` over a number field, with the
split-centre, right Haar invariance and compact additive adele quotient
hypotheses in the statement. Let `R` be any operator realization and `j` a
complex-linear map from its space to quotient `L²`. Assume each `j f` has the
class relation `IsGeneralLinearFormClass` with the actual function realized by
`f`.

For every bounded complex-linear functional `ℓ` on quotient `L²`, the scalar
functions `g ↦ ℓ(ρ(b∞(g)) (j f))`, where `b∞` is the actual matrix archimedean
inclusion transported to the group-scheme point model, give a complex-linear
map `C` from `R.Space` to the smooth functions on the archimedean group.
The map intertwines the actual enveloping actions: `D(C f) = C(D f)` for every
`D`. In particular it is not necessary to assume Hilbert smoothness of the
original vector as a separate premise, or to assume a central character or
irreducibility for `R`.

## Implemented proof

Choose one smooth compact archimedean kernel reproducing the stable form `f`
at every adelic point. At the point `x`, the function in the archimedean
parameter is the left translate of the smooth slice at the finite coordinate
of `x`. Differentiation of the reproduced convolution transfers `D` to the
kernel, and left-translation covariance gives the value of `D f` at
`x · b∞(g)` from the weight `w(z) = (D κ)(z⁻¹ g)`. This weight is continuous
and compactly supported, since the differential preserves compact support and
`z ↦ z⁻¹ g` is a homeomorphism.

The weighted quotient representative comparison identifies the quotient class
of the weighted pointwise integral with the Bochner integral of the weighted
orbit of `j f`. After pulling back to adelic points the differentiated
reproduction identity shows that this is the same continuous function as the
translate of `D f` by `b∞(g)`. Uniqueness of the class and compatibility with
right translation give equality of that Bochner integral with the genuine
translate of `j(D f)`.

The actual scalar coefficient is continuous by continuity of the quotient
orbit and of `ℓ`. Convolve it with the same kernel, and transfer all enveloping
differentials to the kernel. Since `ℓ` commutes with the integrals of the
weighted classes, the differentiated scalar convolution is exactly the
coefficient of `D f`. Taking `D = 1` identifies the scalar convolution itself
with the original coefficient. Its pointwise formula also gives linearity
in `f`, hence the desired smooth-function-valued map.

## Provenance and scope

This is a derived step for the passage from the operator orbit to its Hilbert
closure in the summand-to-realization direction of Getz–Hahn, *An Introduction
to Automorphic Representations*, Springer GTM 300 (2024), Theorem 9.7.3,
pp. 265–267 (PDF pp. 277–279), especially the role of the algebraic vectors in
(9.40). It uses compact reproduction on the original quotient, rather than the
Library's separate determinant-band proof of scalar-coefficient smoothness.
It does not assert the existence of the original form representatives in a
Hilbert summand, invariance of a class image's closure, or algebraic
irreducibility.
