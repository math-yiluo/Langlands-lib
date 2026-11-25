/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
import WeilConjectures.AlgebraicGeometry.SfbAdicCompleteStratumGluing
import WeilConjectures.AlgebraicGeometry.SfbPerfectModelCompletionTransport

/-! # Completeness from stratified perfect models

Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Stratified completed perfect models are locally derived complete.
Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication; Lemma 6.5.8.
(auxiliary; not a blueprint node).

Proof: unpack the stratum covers and their finite-projective coefficient complexes.
The strict bounds imply degreewise vanishing outside the same interval, so
adicPerfectModel_complete_reduction applies. Its HasCompleteResidueCalculation
contains completeness of the normalized model. The presentation comparison
sfbPerfectModel_completion_transport transfers this to sfbCompletedModel. On every
covering arrow, the original witness identifies the restriction of K with that of
this complete object. Apply sfbAdicComplete_of_stratum_local_iso to these witnesses.
Its proof uses preservation and detection of the completion unit on the finite
strata and their covers; the empty scheme requires no separate nonemptiness hypothesis. -/
theorem adicPerfectModels_completeness (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.IsMaximal ∧ ∀ J : Ideal A, J.IsMaximal → J = I)
    [IsAdicComplete I A]
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)))
    (hK : IsSfbStratifiedPerfect X I K) :
    IsSfbAdicComplete X I K := by
  classical
  obtain ⟨s, _, hmodels⟩ := hK
  choose V hV hm using hmodels
  apply sfbAdicComplete_of_stratum_local_iso X A I s V hV K
  intro α U f hf
  obtain ⟨P, a, b, _, ha, hb, hP, e⟩ := hm α U f hf
  refine ⟨sfbCompletedModel X I P, ?_, e⟩
  apply (sfbPerfectModel_completion_transport X A I P).mpr
  have hbounded (q : ℤ) (hq : q < a ∨ b < q) : IsZero (P.X q) := by
    rcases hq with hq | hq
    · exact (P.isStrictlyGE_iff a).mp ha q hq
    · exact (P.isStrictlyLE_iff b).mp hb q hq
  obtain ⟨c, _, _, hc, _⟩ := adicPerfectModel_complete_reduction.{u, 0}
    X A I hI.1 P a b hbounded (fun q ↦ ⟨(hP q).2, (hP q).1⟩)
  exact hc.1

end AlgebraicGeometry.Scheme
