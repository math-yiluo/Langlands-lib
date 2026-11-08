# Cuspidal trace class of convolution products from Hilbert–Schmidt convolutions

`Langlands.Automorphic.GroupSchemeFunctions.GroupSchemeFullAEL2CuspidalTraceClassStatement`
is a proposition definition. It supplies no proof.

## Setting

The objects are the Library's actual full almost-everywhere cuspidal space
and its right action, exactly as in
`GroupSchemeFullAEL2CuspidalDecompositionStatement`. The hypotheses are
those of `GroupSchemeFullAEL2Integrated`:

- `F` is a number field and `G` a connected reductive affine group scheme
  over `Spec F`, locally of finite type.
- The parabolic–cocharacter theorem `ParabolicDynamicStatement` is an
  explicit argument.
- `T` is a split central torus with injective, finite-index character
  restriction.
- The Haar measure on the norm-one subgroup is right invariant.

`fullAEL2CuspidalSubmodule` is the closed subspace of
`L²(PositiveRationalQuotient)` of classes whose actual mass-one constant
terms along every proper rational parabolic vanish almost everywhere, with
its published completeness. `fullAEL2CuspidalIntegratedAction … μG f hf` is
the existing operator `R(f)` on that space for the Haar measure `μG` of
`G(A_F)`.

## Hypothesis and conclusion

The hypothesis is that for every compactly supported continuous
`f : C_c(G(A_F), ℂ)`, the cuspidal operator `R(f)` is Hilbert–Schmidt in the
sense of `Langlands.Analysis.OperatorIdeals.IsHilbertSchmidt`.

The conclusion is that for all `f₁ f₂ : C_c(G(A_F), ℂ)` the Haar
convolution `f₁ ⋆ f₂ : g ↦ ∫ a, f₁ a * f₂ (a⁻¹ * g) ∂μG` is integrable and
the cuspidal operator `R(f₁ ⋆ f₂)` is trace class in the sense of
`Langlands.Analysis.OperatorIdeals.IsTraceClass`.

No Hilbert–Schmidt property, rapid decay or reduction theory is proved
here; the hypothesis is the remaining analytic input. Neither the
Dixmier–Malliavin factorization of a general smooth weight nor a trace
formula is asserted.

## Sources and provenance

This is a derived statement. The source is Getz–Hahn, *An Introduction to
Automorphic Representations* (2024), registered as
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.

- Theorem 9.1.2, printed p.241 (one-based PDF p.253): the cuspidal
  restriction `R_cusp(f)` is trace class for every
  `f ∈ C_c^∞(A_G \ G(A_F))`.
- The end of its proof in §9.5 (PDF p.274) and the proof of Lemma 9.3.3
  (printed pp.247–248, PDF pp.259–260): having shown that `R_cusp(f)` is
  Hilbert–Schmidt, the source writes `f` as a finite sum of convolutions
  `h₁ ∗ h₂` (Dixmier–Malliavin, Exercise 9.8) and concludes because a
  product of two Hilbert–Schmidt operators is trace class (Exercise 9.2).

The statement records that last step, "Hilbert–Schmidt for every weight
implies trace class for convolution products", on the actual Library
objects, for compactly supported continuous weights on `G(A_F)`. The
convolution is the left Haar form of Getz–Hahn (3.9), explained in
`Langlands.Analysis.IntegratedActionConvolutionStatement`. The
almost-everywhere cuspidality condition is the one implemented in
`GroupSchemeFullAEL2` and inherited unchanged.

## Intended proof

A private proof compiles. Compactly supported continuous weights are Haar
integrable. The separately staged convolution statement
`IntegratedActionConvolutionStatement`, applied to the cuspidal right action
`fullAEL2CuspidalBoundedRightAction` on the complete cuspidal space, gives
integrability of `f₁ ⋆ f₂` and `R(f₁ ⋆ f₂) = R(f₁) ∘ R(f₂)`. The hypothesis
makes both factors Hilbert–Schmidt, and the published
`Langlands.Analysis.OperatorIdeals.hilbertSchmidtProductTraceClass` makes
their composition trace class.
