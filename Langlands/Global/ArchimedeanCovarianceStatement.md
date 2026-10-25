# Right-translation covariance of the actual enveloping and center actions

Author: Worker 381. Module: `Langlands.Global.ArchimedeanCovarianceStatement`.
Namespace: `Langlands.Global.ArchimedeanGL`.

This module states, without proving, that right translation on actual smooth
archimedean functions intertwines the universal enveloping differential action
with its adjoint twist, and that the same holds for the action of the
enveloping center. All three declarations are Prop-valued definitions; no
theorem is asserted and no proof is implemented in this unit.

## Parameters and objects

Every declaration takes `K : Type u` with `[Field K] [NumberField K]`, in an
arbitrary universe `u`, and `n : ℕ`. Every natural rank is allowed, including
`n = 0` with the existing empty-matrix conventions. The statements use only the
published objects below; no abstract representation, action or compatibility
hypothesis is introduced.

- `InfiniteAdelicGL K n` is `GL_n` of the completion-based infinite adele ring.
- `SmoothFunctions K n` is the published space of complex-valued functions on
  that group that are real-smooth in the mixed real and complex coordinates
  `archimedeanGLCoordinates K n`.
- `R(g) = smoothRightAction K n g` is positive right translation,
  `(R(g) f)(x) = f(x * g)`.
- `D(a) = envelopingAction K n a` is `UniversalEnvelopingAlgebra.lift ℂ` of the
  complex-linear extension `complexSmoothLieAction K n` of the actual real
  directional differential. By `envelopingAction_real_generator`, a real
  generator `envelopingGenerator K n (complexify K n X)` acts by
  `smoothDifferential K n X`, which differentiates at `x` in the matrix
  direction `x * X`.
- `AdU(g) = envelopingConjugation K n g` is the complex algebra automorphism of
  `EnvelopingAlgebra K n` lifting `complexLieConjugation K n g`, the coefficient
  base change of `realLieConjugation K n g`. Writing `C(g)` for the coordinate
  matrix of `g` and `M = realLieAlgebraToMatrix K n`,
  `realLieConjugation_apply` gives `M.symm (C(g) * M X * C(g⁻¹))`, i.e. the
  convention `Ad(g) X = g X g⁻¹`.
- `centerAction K n z` is `envelopingAction K n (centerInclusion K n z)`
  (`centerAction_apply`), and `AdZ(g) = centerConjugation K n g` is the
  restriction of `AdU(g)` to `EnvelopingCenter K n`.

## The statements

`EnvelopingRightCovarianceStatement K n` asserts: for every
`g : InfiniteAdelicGL K n`, every `a : EnvelopingAlgebra K n` and every
`f : SmoothFunctions K n`,

`smoothRightAction K n g (envelopingAction K n a f) =
  envelopingAction K n (envelopingConjugation K n g a) (smoothRightAction K n g f)`,

that is, `R(g) (D(a) f) = D(AdU(g) a) (R(g) f)`.

`CenterRightCovarianceStatement K n` asserts: for every `g`, every
`z : EnvelopingCenter K n` and every `f : SmoothFunctions K n`,

`smoothRightAction K n g (centerAction K n z f) =
  centerAction K n (centerConjugation K n g z) (smoothRightAction K n g f)`.

`EnvelopingCenterRightCovarianceStatement K n` is exactly the conjunction
`EnvelopingRightCovarianceStatement K n ∧ CenterRightCovarianceStatement K n`,
in that order. It is the single target for a subsequent proof.

The statements carry no automorphy, compact-finiteness, center-finiteness or
growth hypothesis, and `g` ranges over the whole infinite group, not merely a
compact subgroup. Covariance is the conclusion, not an assumption. The center
statement reindexes the central element through `centerConjugation`; it
neither assumes nor asserts that `g` fixes central elements pointwise.

## Orientation and derived motivation

The orientation follows from the published conventions. For a real direction
`X`, the left side `R(g) (D(X) f)` differentiates `f` at `x * g` in direction
`(x * g) * X`. On the right side, the chain rule for `x ↦ x * g` sends the
direction `x * (g X g⁻¹)` to `(x * g) * X`. This real-generator identity is the
smooth component of the separately published
`Langlands.Automorphic.RealDifferentialCovarianceStatement`, whose proof is a
separate task.

The intended later proof extends that identity in two algebraic steps. First,
complex linearity extends it to `ComplexLieAlgebra K n`, using
`complexSmoothLieAction_tmul` and `complexLieConjugation_tmul`. Second, since
`R(g)` is invertible, `a ↦ R(g) ∘ D(a) ∘ R(g)⁻¹` and `a ↦ D(AdU(g) a)` are both
complex algebra homomorphisms out of the universal enveloping algebra. They
agree on generators by `envelopingAction_generator` and
`envelopingConjugation_generator`, so they agree everywhere by the universal
property. The center statement then follows by applying the enveloping statement
to `centerInclusion K n z` and rewriting with `centerAction_apply` and
`centerInclusion_centerConjugation`. This paragraph is motivation for that
subsequent proof, not a claim that this unit implements it.

## Original source and provenance

The covariance identities are internal derived compatibility statements built
from the actual definitions imported from `Langlands.Global.ArchimedeanAdjoint`
and `Langlands.Global.ArchimedeanEnvelopingAction`. They are not verbatim
assertions of the source below.

A. Borel and H. Jacquet, *Automorphic forms and automorphic representations*,
Corvallis Part I (1979). Section 1.5(1), printed p. 190 (one-based PDF p. 185),
observes that the right translates of an automorphic form by the compact
subgroup satisfy conditions 1.3(a), (c), (d) if and only if the form does. Here
condition (c) is annihilation by a finite-codimension ideal of `Z(g)`.
Sections 4.2(c) and 4.3, printed p. 195 (PDF p. 190), impose the
corresponding adelic condition with an ideal of `Z(g_∞)` and transcribe it to
the archimedean slices. The present statements isolate the compatibility of
the enveloping and center actions with right translation that such arguments
use. Worker 381 read both original pages. No errata note for this source exists
in the current Library's public notes.

Registered source: `borel-jacquet-1979-automorphic`,
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`,
SHA256 `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
