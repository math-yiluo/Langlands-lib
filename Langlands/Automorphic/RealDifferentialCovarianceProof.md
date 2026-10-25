# Proof of right-translation covariance of actual real differentiation

This module proves `Langlands.Automorphic.realDifferentialCovariance`, whose
type is exactly `RealDifferentialCovarianceStatement K n` for every
`(K : Type u) [Field K] [NumberField K]` and every `n : ℕ`, rank zero
included. No differentiability, action or covariance hypothesis is added. The
proof uses the published `ArchimedeanGL.smoothRightAction`,
`ArchimedeanGL.smoothDifferential`, `finiteSmoothRightAction` and
`finiteSmoothEnvelopingAction`; it defines no new action or operator.

Notation: write `C` for `archimedeanGLCoordinates K n`, `M` for
`ArchimedeanGL.realLieAlgebraToMatrix K n`, and `F_f` for
`ArchimedeanGL.coordinateExtension K n f`. By definition
`(R(g) f)(x) = f(x*g)`, and `(D(X) f)(x)` is the Fréchet derivative of `F_f`
at the matrix `C x` in the direction `C x * M X`.

## Ambient chain rule

`ArchimedeanGL.fderiv_comp_mul_right` states: for any function
`f : ArchimedeanMatrix K n → ℂ` and matrices `a g v`, if `f` is real
differentiable at `g * a`, then the derivative of `h ↦ f (h * a)` at `g` in the
direction `v` equals the derivative of `f` at `g * a` in the direction `v * a`.
The proof uses Mathlib's chain rule `fderiv_fun_comp`. Right multiplication by
`a` is the continuous linear map `(ContinuousLinearMap.mul ℝ _).flip a`, so its
derivative is itself.

## Smooth covariance

`ArchimedeanGL.smoothRightAction_smoothDifferential` is the smooth identity
stated by `SmoothRealDifferentialCovarianceStatement`, for all `g`, `X` and `f`:

`R(g) (D(X) f) = D(M⁻¹(C g * M X * C g⁻¹)) (R(g) f)`.

The proof checks the identity on the underlying function at an arbitrary point
`x`. The left side is the derivative of `F_f` at `C(x*g)` in the direction
`C(x*g) * M X`.

For the right side, the ambient function `h ↦ F_f (h * C g)` agrees with
`R(g) f` at every invertible matrix `h`. This holds because `h * C g` is
invertible, because `F_f` evaluates `f` through `C⁻¹` at invertible matrices,
and because `C⁻¹` is multiplicative. The published extension-independence
lemma `smoothDifferential_eq_of_extension` therefore computes the right side
with this ambient function. The coordinate extension is smooth, hence
differentiable, at the invertible matrix `C x * C g = C(x*g)`. The ambient
chain rule then turns the right side into the derivative of `F_f` at
`C x * C g` in the direction `(C x * (C g * M X * C g⁻¹)) * C g`. This step also
uses `M (M⁻¹ Y) = Y`. After rewriting `C(x*g) = C x * C g` and
`C g⁻¹ = (C g)⁻¹`, it remains to show
`C x * C g * M X = C x * (C g * M X * (C g)⁻¹) * C g`. Reassociating and
cancelling the unit inverse `(C g)⁻¹ * C g = 1` proves this.

`ArchimedeanGL.smoothRightAction_smoothDifferential_realLieConjugation`
restates the same identity with the published adjoint map
`ArchimedeanGL.realLieConjugation K n g` from `Langlands.Global.ArchimedeanAdjoint`:
`R(g) (D(X) f) = D(realLieConjugation K n g X) (R(g) f)`. Its proof rewrites
`realLieConjugation_apply` and applies the previous theorem. The covariance
statement itself writes the conjugation explicitly and does not use this map.

## Finite-smooth descent

`finiteSmoothSlice_ofInfinite_rightAction` states that for every
`g : InfiniteAdelicGL K n`, `b : FiniteAdelicGL K n` and finite-smooth `f`,
the slice at `b` of `finiteSmoothRightAction K n (AdelicGL.ofInfinite K n g) f`
is `ArchimedeanGL.smoothRightAction K n g` applied to the slice at `b` of `f`.
Pointwise, both sides evaluate `f`, at `pair a b * pair g 1` and at
`pair (a*g) b` respectively. These points are equal by `AdelicGL.pair_mul` and
`mul_one`.

`finiteSmoothRealDifferentialCovariance` proves
`FiniteSmoothRealDifferentialCovarianceStatement K n`. By the published
injectivity `finiteSmoothSlice_injective`, it suffices to compare the slices at
every `b`. Rewriting with `finiteSmoothSlice_ofInfinite_rightAction`, the
published `finiteSmoothSlice_envelopingAction`, and
`ArchimedeanGL.envelopingAction_real_generator` turns both sides into the
smooth identity for the slice at `b` of `f`. The smooth covariance theorem
then closes the goal.

## Final theorems

`smoothRealDifferentialCovariance` proves
`SmoothRealDifferentialCovarianceStatement K n` by the smooth covariance
theorem. `realDifferentialCovariance` pairs the smooth and finite-smooth
components, in that order. The closing unapplied `example` checks the full
declaration telescope, with an arbitrary universe for `K` and an arbitrary
rank. The proof compiles under default heartbeats and depends only on the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

These are derived implementation results. The provenance of the mathematical
framework is recorded in the paired Markdown of the published statement module
`Langlands.Automorphic.RealDifferentialCovarianceStatement`.
