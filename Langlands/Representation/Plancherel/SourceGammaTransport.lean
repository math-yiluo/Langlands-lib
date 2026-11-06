import Langlands.Representation.Plancherel.SemidirectSourceHaarNormalization
import Langlands.Analysis.Local.QuotientMeasureEquiv

/-! # Exact transport of source-normalized Haar measures and gamma -/

noncomputable section

open MeasureTheory Topology
open scoped ENNReal

namespace Langlands.Plancherel

open Haar HarishChandraSchwartz QuotientIntegration

universe uG uH

variable {G : Type uG} {G' : Type uH} [Group G] [Group G']
  [TopologicalSpace G] [TopologicalSpace G']

/-- The image of the chosen compact open under an actual ambient group
isomorphism, expressed through the existing inverse-image constructor. -/
def sourceCompactImage (e : G ≃ₜ* G') (K : OpenSubgroup G) : OpenSubgroup G' :=
  K.comap e.symm.toMonoidHom e.symm.continuous

@[simp]
theorem mem_sourceCompactImage (e : G ≃ₜ* G') (K : OpenSubgroup G) (g : G) :
    e g ∈ sourceCompactImage e K ↔ g ∈ K := by
  change e.symm (e g) ∈ K ↔ g ∈ K
  rw [e.symm_apply_apply]

theorem sourceCompactImage_isCompact (e : G ≃ₜ* G') (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) :
    IsCompact (sourceCompactImage e K : Set G') :=
  e.symm.toHomeomorph.isCompact_preimage.mpr hK

variable [MeasurableSpace G] [BorelSpace G] [MeasurableSpace G'] [BorelSpace G']

section SubgroupHaar

variable [IsTopologicalGroup G] [IsTopologicalGroup G'] [LocallyCompactSpace G']
  (e : G ≃ₜ* G') (K : OpenSubgroup G) (K' : OpenSubgroup G')
  (hK : IsCompact (K : Set G)) (hK' : IsCompact (K' : Set G'))
  (H : Subgroup G) (H' : Subgroup G')
  (hH : IsClosed (H : Set G)) (hH' : IsClosed (H' : Set G'))
  (hsub : ∀ g : G, e g ∈ H' ↔ g ∈ H)
  (hcompact : ∀ g : G, e g ∈ K' ↔ g ∈ K)

include hcompact in
/-- The existing intrinsic subgroup Haar normalization is preserved exactly
when the ambient group, subgroup and chosen compact open correspond. -/
theorem measurePreserving_sourceSubgroupHaar :
    MeasurePreserving (subgroupContinuousMulEquiv e H H' hsub)
      (subgroupCompactOpenHaar K hK H hH)
      (subgroupCompactOpenHaar K' hK' H' hH') := by
  let eH := subgroupContinuousMulEquiv e H H' hsub
  let sourceMu := subgroupCompactOpenHaar K hK H hH
  have : (Measure.map eH sourceMu).Regular :=
    Measure.Regular.map eH.toHomeomorph
  have : Measure.IsHaarMeasure (Measure.map eH sourceMu) := eH.isHaarMeasure_map sourceMu
  have heHm : Measurable (eH : H → H') := eH.continuous.measurable
  refine ⟨heHm, ?_⟩
  apply compactOpenHaarAlong_eq_of_mass_one K' hK' H'.subtype
    hH'.isClosedEmbedding_subtypeVal
  change (Measure.map (eH : H → H') sourceMu) {h : H' | (h : G') ∈ K'} = 1
  trans sourceMu (eH ⁻¹' {h : H' | (h : G') ∈ K'})
  · exact Measure.map_apply heHm
      ((K'.isOpen.preimage continuous_subtype_val).measurableSet)
  have hpre : eH ⁻¹' {h : H' | (h : G') ∈ K'} = {h : H | (h : G) ∈ K} := by
    ext h
    exact hcompact h
  rw [hpre]
  exact subgroupCompactOpenHaar_mass K hK H hH

end SubgroupHaar

section OpenCell

variable (e : G ≃ₜ* G') {P V : Subgroup G} {P' V' : Subgroup G'}
  (eP : P ≃ₜ* P') (eV : V ≃ₜ* V')
  (heP : ∀ p : P, (eP p : G') = e p)
  (heV : ∀ v : V, (eV v : G') = e v)
  (K : Subgroup G) (K' : Subgroup G')
  (hcompact : ∀ g : G, e g ∈ K' ↔ g ∈ K)
  (sourceP : Measure P) (sourceV : Measure V)
  (targetP : Measure P') (targetV : Measure V')
  (hP : MeasurePreserving eP sourceP targetP)
  (hV : MeasurePreserving eV sourceV targetV)

include heP heV hcompact hP hV in
/-- Transporting the actual two subgroup measures and compact subgroup
preserves the existing open-cell integral, including its scale. -/
theorem openCellConstant_eq_of_transport :
    openCellConstant targetP targetV K' = openCellConstant sourceP sourceV K := by
  unfold openCellConstant
  rw [← hV.lintegral_comp_emb eV.toHomeomorph.measurableEmbedding]
  apply lintegral_congr
  intro v
  rw [← hP.lintegral_comp_emb eP.toHomeomorph.measurableEmbedding]
  apply lintegral_congr
  intro p
  rw [heP, heV, ← map_inv, ← map_mul]
  by_cases hx : (p : G) * (v : G)⁻¹ ∈ K
  · rw [Set.indicator_of_mem (show e ((p : G) * (v : G)⁻¹) ∈ (K' : Set G') from
      (hcompact _).mpr hx), Set.indicator_of_mem hx]
    rfl
  · rw [Set.indicator_of_notMem (show e ((p : G) * (v : G)⁻¹) ∉ (K' : Set G') from
      fun h => hx ((hcompact _).mp h)), Set.indicator_of_notMem hx]

end OpenCell

section NormalizedGamma

variable [IsTopologicalGroup G] [IsTopologicalGroup G'] [LocallyCompactSpace G']
  (e : G ≃ₜ* G') (K : OpenSubgroup G) (K' : OpenSubgroup G')
  (hK : IsCompact (K : Set G)) (hK' : IsCompact (K' : Set G'))
  {P V : Subgroup G} {P' V' : Subgroup G'}
  (hP : IsClosed (P : Set G)) (hV : IsClosed (V : Set G))
  (hP' : IsClosed (P' : Set G')) (hV' : IsClosed (V' : Set G'))
  (hpar : ∀ g : G, e g ∈ P' ↔ g ∈ P)
  (hopp : ∀ g : G, e g ∈ V' ↔ g ∈ V)
  (hcompact : ∀ g : G, e g ∈ K' ↔ g ∈ K)

include hpar hopp hcompact in
/-- Common-compact source gammas agree under the actual ambient transport.
No open-cell conullness, convergence or component choice is needed. -/
theorem compactNormalizedSourceGamma_eq_of_transport :
    compactNormalizedSourceGamma hP' K' hK' V' hV' =
      compactNormalizedSourceGamma hP K hK V hV := by
  exact openCellConstant_eq_of_transport e
    (subgroupContinuousMulEquiv e P P' hpar)
    (subgroupContinuousMulEquiv e V V' hopp)
    (fun _ => rfl) (fun _ => rfl) K K' hcompact
    (subgroupCompactOpenHaar K hK P hP) (subgroupCompactOpenHaar K hK V hV)
    (subgroupCompactOpenHaar K' hK' P' hP') (subgroupCompactOpenHaar K' hK' V' hV')
    (measurePreserving_sourceSubgroupHaar e K K' hK hK' P P' hP hP' hpar hcompact)
    (measurePreserving_sourceSubgroupHaar e K K' hK hK' V V' hV hV' hopp hcompact)

end NormalizedGamma

end Langlands.Plancherel
