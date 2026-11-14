# Bottom-degree classes for creation and shuffle slant

This internal extension supplies degree-zero cocycle classes for the ordered
Čech complex of a scheme over a commutative ring. `cyclesOfKerZero` lifts the
kernel of its degree-zero differential to the actual cycles object, and
`classMapZero` applies the homology projection. With a finite affine cover of
a separated scheme, `canonicalClassZero` transports structure-sheaf classes to
actual right-derived cohomology.

`oneZeroCocycle` is the constant section one, closed by `Cech.d_one`.
`unitH` is its class and `unitCanonical` its actual-cohomology image.
The lemmas `creationByCocycle_unitH`, `creationH_unitH` and
`creationCanonical_unitCanonical` prove that creation on this class returns its
creating degree-one class. The proof computes cup on the unit cocycle and uses
the cycles-map formula for creation.

For a product diagram and the section algebra, finite affine cover and
functional hypotheses of `AllSeqSlant`, `slantCochainMap_mem_ker_zero` proves
that slant sends a one-cocycle to a zero-cocycle. The proof uses the degree-zero
instance of the anticommutation identity. `slantH_classMap_bottom` identifies
the induced homology class with `classMapZero` of this zero-cocycle by the
cycles-map formula and injectivity of the cycles inclusion.
`slantCanonical_canonicalClass_bottom` transports that equality to actual
cohomology.

The raw bottom-degree evaluations are
\[
 L_0(p_1^*z)(b)=l(z)\,1_{V_b},\qquad L_0(p_2^*y)=0,
\]
where the first formula holds for every one-cochain \(z\), and the second
requires \(y\) to be a one-cocycle. They are implemented as
`KunnethDetection.L_bottom_pull_left` and `L_bottom_pull_right`.
The bottom shuffle has one summand. Its first-factor path is the identity,
so the first equality is `slant_mul` with second factor one after restriction
and pullback compatibility. Its second-factor path is constant, so the
second equality follows from `cocycle_apply_const` and zero preservation.

Over a field, let \(\ell\) be a dual of actual first cohomology of the first
factor, using the fixed extension `h1DualCochainFunctional`. The lemmas
`slantByH1Dual_bottom_pull_left` and `slantByH1Dual_bottom_pull_right` give
\[
 \operatorname{slant}_{\ell,0}(p_1^*x)=\ell(x)\,\operatorname{unitCanonical},
 \qquad
 \operatorname{slant}_{\ell,0}(p_2^*y)=0
\]
for all actual degree-one classes on the two factors. The proofs choose
cocycle representatives, use the actual pullback representative formula and
the bottom slant formula, and then apply the raw evaluations. The first also
uses `h1DualCochainFunctional_cocycle` to identify the scalar.

The provenance is internal: these constructions extend the positive-degree
class interface in `AllSeqCup` and `AllSeqSlant`, using the existing creation,
slant, and actual pullback maps. No exterior generation or geometric dimension
equality is assumed. General creation-contraction relations are not proved.
