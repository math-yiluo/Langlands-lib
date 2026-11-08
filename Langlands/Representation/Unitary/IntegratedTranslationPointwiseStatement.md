# Pointwise representatives of integrated translation actions

`Langlands.Analysis.IntegratedTranslationPointwiseStatement` is a
proposition definition. It supplies no proof.

## Setting

- `X` is a measurable space with a σ-finite measure `μX`.
- `G` is a group with a measurable structure and a σ-finite measure `μ`.
  No topology, Haar property or invariance of `μ` is assumed.
- `act : X → G → X` is jointly measurable as a map on `X × G`. For every
  `g`, the map `x ↦ act x g` preserves `μX`. No action laws are imposed,
  because the statement does not use them.
- `π : G →* (Lp ℂ 2 μX →L[ℂ] Lp ℂ 2 μX)` is an actual representation by
  bounded operators. It must preserve norms vectorwise and have almost
  everywhere strongly measurable orbits. These are exactly the inputs of
  the existing `integratedIsometricAction`.
- The compatibility hypothesis says that, for every `g` and every `L²`
  class `φ`, the class `π g φ` is represented almost everywhere by
  `x ↦ φ (act x g)`. Here `φ` denotes Mathlib's chosen representative.
- `f : G → ℂ` is `μ`-integrable.

## Conclusion

For every `L²` class `φ`:

1. for `μX`-almost every `x`, the function `g ↦ f g * φ (act x g)` is
   `μ`-integrable;
2. the class `integratedIsometricAction μ π _ _ f hf φ`, which is the
   Bochner integral `∫ g, f g • π g φ ∂μ` in `L²`, is represented
   `μX`-almost everywhere by `x ↦ ∫ g, f g * φ (act x g) ∂μ`.

The second conclusion is stated for Mathlib's representative of the
integrated class and for the pointwise Bochner integral of scalars. Where
part 1 fails, that scalar integral is Mathlib's junk value zero; part 1
shows this happens only on a null set. No continuity, boundedness or
smoothness of the pointwise integral is asserted.

The universes of `X` and `G` are independent.

## Provenance and intended use

This is an internal analytic target, so no original source states it.
Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
registered as `getz-hahn-2024-automorphic-representations`, uses the
pointwise convolution formula for `R(f)φ` throughout Chapter 9.
Examples are Lemma 9.3.3 on printed pp.247–248 and Theorem 9.6.4 on
printed p.264. The Library's integrated actions on the actual quotient
`L²` spaces are vector-valued Bochner integrals, such as
`haarQuotientL2IntegratedAction` in `GroupSchemeQuotientL2Integrated`. This
proposition is the bridge between the two. Its intended consumers are a
bounded-continuous smoothing lift on compact quotients, for the published
`HilbertSchmidtBoundedContinuousLiftStatement` criterion, and the smooth
representative of `R(f)φ` used in rapid-decay arguments.

## Intended proof

A private proof compiles. It replaces `f` by a strongly measurable
version and uses Mathlib's strongly measurable representative of `φ`. Then
`(x, g) ↦ f g * φ (act x g)` is strongly measurable on `X × G`.

On a measurable set `B` of finite `μX`-measure, Hölder's inequality and
measure preservation give
`∫⁻ x in B, ‖φ (act x g)‖ₑ ≤ μX B ^ (1/2) · ‖φ‖₂` for every `g`. By Tonelli,
the absolute double integral over `B × G` is at most
`μX B ^ (1/2) · ‖φ‖₂ · ‖f‖₁`. σ-finiteness of `μX` then gives part 1.

For part 2, both sides are integrable on every finite-measure set. Their
set integrals agree: pair the Bochner integral with the `L²` indicator of
`B`, move the pairing inside the integral, use the compatibility
hypothesis, and apply Fubini on `B × G`. Mathlib's
`ae_eq_of_forall_setIntegral_eq_of_sigmaFinite` concludes.
