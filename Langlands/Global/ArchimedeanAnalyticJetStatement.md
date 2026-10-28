# Analytic uniqueness from vanishing actual matrix jets

`Langlands.Global.ArchimedeanGL.AnalyticMatrixJetUniquenessStatement K n`
is a proposition for an arbitrary number field `K : Type u` and every
natural rank `n`, including `n = 0`. It uses only published carriers:
the actual smooth functions `SmoothFunctions K n`, the coordinate
homeomorphism `archimedeanGLCoordinates K n` from the completion-based
group `GL_n(InfiniteAdeleRing K)` to the mixed-coordinate group
`ArchimedeanGL K n`, and the ambient expression
`coordinateExtension K n f : ArchimedeanMatrix K n → ℂ`. None of these is
modified, and the statement does not depend on the unpublished Casimir,
Cartan-symbol or polynomial-annihilation drafts.

## The proposition

For every `f : SmoothFunctions K n` and every basepoint
`x₀ : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)`,
assume:

1. For every `g : ArchimedeanGL K n`, the function
   `coordinateExtension K n f` is real analytic (`AnalyticAt ℝ`) at the
   unit matrix `(g : ArchimedeanMatrix K n)`.
2. For every `m : ℕ`, the `m`-th iterated real Fréchet derivative
   `iteratedFDeriv ℝ m (coordinateExtension K n f)` at the unit matrix
   `(archimedeanGLCoordinates K n x₀ : ArchimedeanMatrix K n)` is the zero
   continuous real-multilinear map.

Then `f.val x = 0` for every `x ∈ connectedComponent x₀`.

## Conventions and exact scope

- The ambient space `ArchimedeanMatrix K n` keeps its published structure:
  entries in the mixed space of `K`, the `L^∞` operator norm opened by
  `Matrix.Norms.Operator` (as in `ArchimedeanSmoothDifferential`), and the
  product topology. Function values stay complex; analyticity and
  derivatives are over `ℝ`.
- The jet hypothesis includes order `m = 0`, so it contains
  `f.val x₀ = 0` (by `coordinateExtension_apply`). Each order asks for the
  whole multilinear map to vanish, i.e. on every tuple of real matrix
  directions, not only along chosen directions such as the Lie-algebra
  directions used by the published differentials.
- Analyticity is assumed only at invertible matrices, where
  `coordinateExtension_apply` identifies the extension with `f`. Its
  values at non-invertible matrices are arbitrary and are not used.
- The conclusion is restricted to `connectedComponent x₀` in the existing
  topology of `GL_n(InfiniteAdeleRing K)`. No connectedness of this group
  is asserted and no component is discarded.

## Provenance

This is an internal specialization of the identity theorem for real
analytic functions of several variables to the published coordinates; it
claims no external literature theorem in this form. It was formulated by
Worker 94 as a focused prerequisite of the automorphic differential-growth
task `e0d3fab3-d5c8-47ae-bd65-d85037d6fd80` (see `notes/automorphic/differential-growth-source-map.md`, which
keeps analytic regularity, jet uniqueness and orbit density separate), and
published through task `a3cac324-f314-4528-bf45-2750129b42be`.

A prospective proof: analyticity at the basepoint together with the zero
jet gives local vanishing, through the pinned Mathlib
`HasFPowerSeriesOnBall.hasSum_iteratedFDeriv`. The continuous map
`x ↦ (archimedeanGLCoordinates K n x : ArchimedeanMatrix K n)` sends
`connectedComponent x₀` to a preconnected set of unit matrices, on which
the extension is analytic at every point. The several-variable theorem
`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` propagates
the local vanishing to this image, and `coordinateExtension_apply`
transfers it back to `f`. No proof is included here; it is a separate
task after independent publication of this statement.

## What is not stated

This module defines only the conditional proposition. It does not derive
analyticity from joint differential finiteness or from any differential
equation, prove elliptic analytic regularity, or infer analyticity of
arbitrary smooth functions. It does not identify the published enveloping
derivatives with all ambient jets. Lie-orbit density, reproduction and the
final automorphic differential-growth theorem remain separate obligations.
