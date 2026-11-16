# Right derivatives under signed real reversal

This internal supporting unit concerns the actual group `G = GL₃(ℝ)` and its
matrix space `A`, in the namespace `Langlands.Archimedean.RealMixedSwapTwist`.
It derives its formulas from the Library right derivative and the signed
reversal defined in `RealMixedSwapSigned`; it assumes no representation-theoretic
classification or intertwining-operator theorem.

## Direction map and unsigned pullback

`reverseDirection : A →ₗ[ℝ] A` sends `X` to `-Xᵀ`.
`reverseDirection_involutive` proves that applying it twice is the identity.

Recall `twist g = w (gᵀ)⁻¹`, for the determinant-one signed reversal matrix
from `RealMixedSwapTwist`, and `twistLin f = f ∘ twist`.
For every smooth complex-valued function `f`, matrix direction `X`, and `g : G`,
`rightDerivative_twistLin` proves

`R_X(twistLin f)(g) = R_(-Xᵀ) f (twist g)`.

The proof uses the matrix-coordinate formula
`R_X f(g) = d(unitsExtension f)_g (gX)` from
`PrincipalSeriesStability`. On the open set of invertible matrices, the
extension of `twistLin f` agrees locally with the extension of `f` composed
with `B(Y) = w (Ring.inverse Y)ᵀ`. The derivative of matrix inversion and the
chain rule give the tangent matrix
`w (-(g⁻¹ (gX) g⁻¹))ᵀ`. Cancelling `g⁻¹g` makes this equal to
`(twist g)(-Xᵀ)`, giving the stated right derivative.

## Signed pullback

Recall `signDet g = det(g)/|det(g)|`, coerced from `ℝ` to `ℂ`, and
`signedTwistLin q f g = signDet g ^ q * f (twist g)` for `q : ℕ`.
`eventually_signDet_ratio` proves that the matrix function
`Y ↦ det(Y)/|det(Y)|` agrees with the constant `signDet g` on a neighborhood
of every invertible `g`. The proof uses continuity of the determinant and
separates its positive and negative cases; its value is respectively `1`
or `-1` on those neighborhoods.

Consequently, for every `q : ℕ`, smooth `f`, `X : A`, and `g : G`,
`rightDerivative_signedTwistLin` proves

`R_X(signedTwistLin q f)(g) = signDet g ^ q * R_(-Xᵀ) f (twist g)`.

In matrix coordinates the signed extension agrees locally with the unsigned
extension multiplied by the constant `signDet g ^ q`. The derivative of
this constant multiple followed by the unsigned identity proves the formula.
The determinant sign contributes no derivative term.

`rightDerivative_signedTwistLin_eq` gives the corresponding equality of
functions. By applying it to `-Xᵀ`, `signedTwistLin_rightDerivative` gives

`signedTwistLin q (R_X f) = R_(reverseDirection X) (signedTwistLin q f)`.

## Scope

These are derivative transport identities for smooth functions. They construct
no injective intertwiner between distinct parameter modules and do not prove
`RealInducedCharacterSwapStatement`. They supply the Lie-action identity
needed when conjugating such an intertwiner by signed reversal.
