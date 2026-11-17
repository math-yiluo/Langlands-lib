# Rectangular Mellin convergence for adelic simple-root gauges

`adelicSimpleRootGaugeRectangularMellin` proves exactly the published proposition
`AdelicSimpleRootGaugeRectangularMellinStatement`, with no additional analytic
premise. The proof retains the arbitrary universe, every number field with
compact additive adelic quotient, every `t<r`, every nonnegative real `τ`, the
actual adelic points, and the published rectangle and Whittaker quotient
measures.

A sufficient common threshold is

`C = max 0 (τ + 3 + ∑ j : Fin (t+1), (j+1)*(t-j))`.

The natural multiplicities in this formula are cast to real numbers. The
existential choice of `C` precedes the gauge quantifier. The Schwartz function
and all majorant constants may depend on the gauge; `C` does not.

## The rectangle estimate used by the proof

Write `r=t+1+d`, and let `b` be the leading diagonal tuple. The supporting
`RectangularGaugeProductBound` module proves that every gauge admits one
rank-one Schwartz–Bruhat function `Ψ` and one finite extended nonnegative
constant `M` such that, for every `b` and real `σ`,

`rectangularLIntegral(Ξ)(diag b) * |det b|^σ`

is at most

`M * (∏ j, ‖Ψ(blockRoot_j(b))‖) * |det b|^(σ-τ)`.

All norms in this integral estimate are interpreted in `ENNReal`. The helper's
rank transport identifies its matrix chart integral with the actual published
`rectangularPoint` integral, rather than changing its measure.

For completeness, the preceding analytic helpers obtain this estimate as
follows. Factor the lower unipotent at `x` as `U*diag(c)*K`, with `U` upper
unitriangular and `K` in the standard compact subgroup. Diagonal conjugation
transfers this same factorization to every leading tuple `b`, with corrected
diagonal equal to the padded tuple `b` times `c`. The actual gauge invariances
identify its value with the corresponding diagonal profile. The last standard
basis row bounds the full idele norm of the last diagonal entry by one.
Multiplying the profile by the determinant norm to `τ` therefore bounds its
scalar weight by the product of actual simple-root norms to the nonnegative
powers `j*τ`.

The rectangular minor estimates bound all finite and archimedean rectangle
coordinates in terms of these actual roots. A denominator for the root row
also gives a common denominator for the rectangle, the diagonal correction
and its inverse, and finally the original leading roots. At infinity the joint
row of original leading roots and all rectangular entries has polynomial
growth in the actual root row. The remaining positive full-idele powers have
polynomial growth on the fixed finite support. Arbitrary Schwartz rapid decay
then supplies the precise hypotheses of the published joint Schwartz-majorant
theorem. Its product-majorant theorem gives the rank-one function `Ψ`.

The product in the rectangle entries has finite integral for the actual
rectangle measure: the entry enumeration is a continuous additive
isomorphism, Haar uniqueness compares the transported measure with a finite
product of rank-one additive Haar measures, and Tonelli reduces finiteness to
rank-one Schwartz integrability. Integrating the normalized pointwise bound
and multiplying by `|det b|^(σ-τ)` gives the displayed estimate. These steps are
implemented in `RectangularNormalizedMajorant`, `RectangleProductMajorant`
and `RectangularGaugeProductBound` and their preceding geometry helpers.

## Torus integration

The current module first proves finite integrability of a product of
rank-one Schwartz Mellin kernels over any Haar measure on the idele torus.
Haar uniqueness transports finiteness to the product of rank-one Haar
measures. Finite product Tonelli and the published rank-one adelic Schwartz
Mellin theorem apply whenever each coordinate exponent is greater than three.

The change to adjacent block roots followed by the final diagonal entry is a
continuous multiplicative isomorphism. It preserves finiteness for arbitrary
Haar normalization, through a positive finite Haar scalar. In these coordinates
the determinant norm has powers `j+1`, and the inverse of the actual diagonal
unipotent Haar modulus contributes powers `-(j+1)*(t-j)`. Consequently the
leading product with determinant exponent `s` has coordinate exponents

`(j+1)*s - (j+1)*(t-j)`.

Every such exponent exceeds three if
`s > 3 + ∑ j, (j+1)*(t-j)`. Taking `s=σ-τ` proves the needed estimate. Applying
the integrated rectangle bound and pulling out its finite constant `M` proves
`IsAdelicSimpleRootGauge.lintegral_rectangular_torus_of_large` with the
actual inverse Haar modulus.

## Whittaker quotient and the target

The function on the smaller group is the actual rectangle integral times
its determinant norm to `σ`. Published rectangle integration gives its
measurability and left unipotent invariance. Its right standard-compact
invariance follows from the published compact-invariance theorem and the
fact that determinant norm equals one on the standard compact subgroup.

Worker 361's `WhittakerStandardCompactTorusIntegral` criterion applies these
properties to the single finite inverse-modulus torus integral just proved.
It gives finiteness on the actual Whittaker quotient measure, evaluated at the
published representatives `p.out`. The final theorem chooses the displayed
nonnegative common threshold and unfolds the actual rectangular integral to
match the target proposition.

No positive-row hypothesis is used. When `d=0`, the same finite-product
argument has no rectangle factors, and the rectangle Haar measure has finite
mass by the same transport argument. Thus this proof includes the zero-row
case without imposing an extra assumption or replacing either published
measure. Independent semantic review, Lake build and exact-target validation
remain the publication checks for this proof.
