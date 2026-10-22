# Harmonic data under a continuous field isomorphism

This module constructs transport of the published harmonic inputs along a supplied
field isomorphism `e : F ≃+* E` with continuous forward and inverse maps, `he` and
`hi`. The two fields may belong to different universes. It supplies a prerequisite
for comparing local-factor inputs across field presentations. It asserts no
comparison of Weil groups, reciprocity maps, conductors or epsilon systems.

The provenance is internal and derived from the existing definitions. No new
literature claim is needed: [Basic](Basic.md) supplies the objects, the plus-sign
Fourier convention and intrinsic self-duality, while
[CharacterTransport](CharacterTransport.md) supplies continuous surjective
character pullback and positive Haar scaling. The generic test-function pullback
is reused from [Hecke test functions](../Representation/Hecke/TestFunction.md).
The proofs below establish
compatibility of these exact constructions with an actual continuous field
isomorphism, using Mathlib change of variables.

## The transported objects

For any homeomorphism `e : X ≃ₜ Y`, the published
`Langlands.Hecke.TestFunction.pullback e.symm` gives
the complex linear equivalence from test functions on `X` to test functions
on `Y`, sending `f` to `f ∘ e.symm`. The reused construction supplies local
constancy, compact support, linearity, forward pullback as inverse, and both
inverse laws. Evaluation in both directions holds by definition:
the equivalence sends `f` at `y` to `f (e.symm y)`, and its inverse sends
`g` at `x` to `g (e x)`.

In namespace `FieldTransport`, `homeomorph e he hi` has exactly the supplied
field isomorphism's forward and inverse maps. The three associated constructions
are:

- `additiveCharacter e hi ψ`, the character `y ↦ ψ(e⁻¹ y)`. The existing
  surjective-pullback constructor proves continuity and nontriviality.
  `additiveCharacter_symm` proves inverse transport, and
  `additiveCharacterEquiv e he hi` packages both directions.
- `testFunctionEquiv e he hi`, the specialization of the preceding complex
  linear equivalence to these fields. Its forward and inverse evaluation
  formulas are explicit simp lemmas.
- `haarMeasure e he hi μ`, the actual pushforward `Measure.map e μ.measure`.
  It is a regular additive Haar measure: additive invariance and the Haar
  conditions use `AddEquiv.isAddHaarMeasure_map`, and regularity uses
  `Measure.Regular.map` for the homeomorphism.

The measure construction and subsequent results assume topological-ring
structures and Borel measurable spaces for both fields. The character and
test-function constructions only need the earlier field and topology assumptions.

`haarMeasure_symm` proves that inverse pushforward returns the original bundled
measure, using the measurable equivalence's `map_symm_map` and extensionality.
`haarMeasureEquiv` packages the resulting equivalence of actual regular Haar
measures. `haarMeasure_scale` proves that transport commutes with scaling by any
supplied positive `NNReal` constant, by `Measure.map_smul`.

## Change of variables and Fourier compatibility

Write `ψ' = ψ ∘ e⁻¹`, `μ' = e_* μ` and `T f = f ∘ e⁻¹`. Then
`integral_haarMeasure` and `integrable_haarMeasure_iff` give

```text
∫_E g(y) dμ'(y) = ∫_F g(e(x)) dμ(x),
Integrable g μ' ↔ Integrable (g ∘ e) μ.
```

They use the measurable embedding associated to the homeomorphism. There is no
extra Jacobian scalar because the measure is itself pushed forward.

`fourierIntegral_transport` proves, for every function `f : F → ℂ`,

```text
FourierIntegral(ψ', μ', T f)(y)
  = FourierIntegral(ψ, μ, f)(e⁻¹ y).
```

The proof changes variables in the actual Bochner integral and rewrites
`e⁻¹(e(x) * y) = x * e⁻¹(y)`. It therefore preserves the kernel `ψ(x*y)`,
including its plus sign. For arbitrary functions the raw integral retains
Mathlib's convention for nonintegrable functions. The corollary
`fourierTransform_transport` applies to actual Schwartz–Bruhat functions.
Their Fourier integrands are integrable by `fourierIntegrand_integrable` in `Basic`,
so this corollary compares convergent integrals.

## Intrinsic self-duality

For this part both fields also have the locally compact, Hausdorff and totally
disconnected instances required by the existing `IsSelfDual` predicate. That
predicate includes convergence of the second Fourier integral and the equality
of Fourier squared with reflection.

`isSelfDual` transports a supplied proof of intrinsic self-duality. Every target
test function is first written as `T f` using the test-function equivalence.
The integrability equivalence and Fourier compatibility transport convergence of
the second integral. Applying the raw Fourier identity to the first transform
then gives Fourier squared, and preservation of negation by `e⁻¹` identifies its
value with `(T f)(-y)`. This proof does not assume that Fourier preserves the test
space.

`isSelfDual_iff` obtains the reverse implication by applying the same argument to
`e⁻¹` and using the character and measure inverse laws:

```text
IsSelfDual ψ' μ' ↔ IsSelfDual ψ μ.
```

Finally, `selfDualMeasureExists_iff` transports witnesses in either direction to
prove equivalence of the published existence propositions for `ψ'` and `ψ`. It
does not prove either existence proposition unconditionally. No character, Haar
measure or epsilon system is selected from an unproved existence assertion.
