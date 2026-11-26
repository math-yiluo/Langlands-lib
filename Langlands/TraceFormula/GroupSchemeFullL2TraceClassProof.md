# Trace class on the full automorphic L² space

`Langlands.TraceFormula.groupSchemeFullL2TraceClass` proves
`Langlands.TraceFormula.GroupSchemeFullL2TraceClassStatement.{u}` for an arbitrary
universe `u`. The theorem uses the Haar measure on the adelic group and the Library's
Haar quotient measure on `[G]`.

## Proof

Each continuous compactly supported factor is integrable for Haar measure.
`Langlands.Analysis.integratedActionConvolution` then provides an integrability witness
for the left Haar convolution and identifies its integrated operator with
`R(f₁) ∘ R(f₂)`. The representation in this application is the bounded right action
`haarQuotientL2BoundedRightAction`, with its norm-preserving and orbit-measurability
lemmas. The convolution theorem uses measurable multiplication and inversion on the
adelic group and the s-finiteness and left invariance of its Haar measure.

Write `H = L²([G])`, `S = fullAEL2CuspidalSubmodule`, `P : H → S` for the
orthogonal projection and `ι : S → H` for the inclusion. For each `v ∈ H`,
`groupSchemeCuspidalImage` uses the vanishing translated radical integrals of `f₂`
to place `R(f₂)v` in `S`. The proof views this vector as `w ∈ S` and uses
`fullAEL2CuspidalOrthogonalProjection_inclusion` to identify `P(R(f₂)v)` with `w`.
By `fullAEL2CuspidalOrthogonalProjection_integratedAction`, this is also
`R_cusp(f₂)(Pv)`. Applying `R(f₁)` to `ιw` gives `ι(R_cusp(f₁)w)` by
`fullAEL2CuspidalIntegratedAction_val`. These pointwise equalities give the operator
identity

`R(f₁ * f₂) = (ι ∘ R_cusp(f₁)) ∘ (R_cusp(f₂) ∘ P)`.

The Hilbert–Schmidt ideal lemmas `isHilbertSchmidt_precomp` and
`isHilbertSchmidt_postcomp` apply to the bounded projection and inclusion,
respectively. Thus the two factors `H → S` and `S → H` are Hilbert–Schmidt by
the hypotheses on `R_cusp(f₂)` and `R_cusp(f₁)`. The rectangular product theorem
`hilbertSchmidtProductTraceClass` makes their composite trace class on `H`.

## Relation to Getz–Hahn

Getz–Hahn, *An Introduction to Automorphic Representations* (2024), is registered as
`getz-hahn-2024-automorphic-representations`. The retained PDF has SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.

- Lemma 9.3.3, printed pp. 247–248 (PDF pp. 259–260), uses convolution products of
  Hilbert–Schmidt operators in the proof of cuspidal trace class in Theorem 9.1.2,
  printed p. 241 (PDF p. 253). The formal proof takes the Hilbert–Schmidt properties
  of the two cuspidal actions as hypotheses and applies the product argument on
  `H` using the maps through `S`.
- Lemma 16.4.2, printed p. 430 (PDF p. 438), unfolds the radical period and obtains
  cancellation from a supercuspidal factor at a finite place. Here the corresponding
  adelic cancellation for `f₂` is given directly for every proper rational parabolic
  and every two-sided translate. The cuspidal-image theorem supplies the resulting
  membership in `S` for the Library's continuous compactly supported weights on the
  ambient adelic group.
- Theorem 18.2.5, printed p. 479 (PDF p. 486), assumes cuspidal image for its simple
  relative trace formula. Section 18.5, printed pp. 487–488 (PDF pp. 494–495), uses
  Theorem 9.1.2 for the trace-class cuspidal restriction in the twisted setting and
  assumes cuspidal image in Corollary 18.5.1. The formal proposition gives the trace
  class of the convolution operator on the full quotient space in the stated setting.
