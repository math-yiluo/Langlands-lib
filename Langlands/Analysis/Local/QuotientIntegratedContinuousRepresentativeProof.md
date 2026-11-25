# Proof of continuous representatives on a coset space

This module proves
`Langlands.QuotientIntegration.QuotientIntegratedContinuousRepresentativeStatement`
(module `Langlands.Analysis.Local.QuotientIntegratedContinuousRepresentativeStatement`)
as `Langlands.QuotientIntegration.quotientIntegratedContinuousRepresentative`.

## Implemented proof

Write `R(f)` for the integrated isometric action and
`S = tsupport f · (tsupport f)⁻¹`. The notation `H ∩ x S x⁻¹` below denotes
the preimage of `x S x⁻¹` in the subgroup `H`.

1. `Langlands.QuotientIntegration.quotientConvolutionKernel` (proving
   `QuotientConvolutionKernelStatement`) gives a continuous
   `v : G → L²(ν)` with `⟪v x, φ⟫ = ∫ f(a) φ(H (x a)) dμG(a)` and
   `‖v x‖² ≤ M · (∫ ‖f(a)‖ dμG(a)) · μH.real (H ∩ x S x⁻¹)` for
   every uniform bound `M` on `‖f‖`.
2. For `h ∈ H`, `Quotient.sound` and `QuotientGroup.rightRel_apply` give
   `H (h y) = H y`, so `⟪v (h x), φ⟫ = ⟪v x, φ⟫`. The function descends
   (`descend`) to `ψ`, continuous by `Continuous.inner` and
   `Continuous.quotient_lift`.
3. The coset space is locally compact (`leftQuotient_locallyCompactSpace`)
   and second countable (`TopologicalSpace.Quotient.secondCountableTopology`
   with the open quotient map), so the measure `ν`, finite on compacts, is
   σ-finite. The action `(q, a) ↦ q a` is continuous because its
   composite with the open quotient map `G × G → LeftQuotient H × G` is
   `(x, a) ↦ H (x a)`. `Langlands.Analysis.integratedTranslationPointwise`
   (proving `IntegratedTranslationPointwiseStatement`) applies to this
   measurable action, with measure preservation from
   `IsCompatible.right_invariant`. It identifies `R(f)φ` almost everywhere
   with `q ↦ ∫ f(a) φ(q a) dμG(a)`. That integral equals `ψ q` for every
   `q` by `Quotient.inductionOn` and the pairing formula in step 1.
4. `norm_inner_le_norm` gives `‖ψ (H x)‖ ≤ ‖v x‖ ‖φ‖`; squaring and the
   bound of step 1 give the stated estimate.

## Provenance

Getz and Hahn use bounded point evaluations in Lemma 9.3.3 and (9.13),
printed pp. 247–248 (PDF pp. 259–260). The first line of (9.14), printed
p. 250 (PDF p. 262), expresses the convolution as an integral. The
general coset-space formulation and explicit subgroup-measure bound are
internal to the Library. The Lean proof obtains the bound from the
published quotient kernel and identifies the integrated class using the
published almost-everywhere comparison. [J. R. Getz and H. Hahn, *An
Introduction to Automorphic Representations* (2024)](https://doi.org/10.1007/978-3-031-41153-3).

Registered source `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
