import Langlands.Global.LeftCosetProductMeasureStatement

/-! # Exact discrete left-quotient product measure -/

noncomputable section

set_option autoImplicit false

open MeasureTheory Topology Set
open scoped Pointwise

namespace Langlands.Global.LeftCosetSpace

universe u v w

/-- Push a Borel product fundamental domain through the supplied group isomorphism. -/
theorem productQuotientMeasure : ProductQuotientMeasureStatement.{u, v, w} := by
  intro A N G gA gN gG tA tN tG tgN tgG mA mN mG bA bN bG scN scG
    E H Γ hΓ hHdisc hΓdisc μA μN sfA sfN μG invG hE
  let D := fundamentalDomain H hHdisc
  let S := E '' (Set.univ ×ˢ D)
  let e := E.toHomeomorph.toMeasurableEquiv
  have hD : MeasurableSet D := measurableSet_fundamentalDomain H hHdisc
  have hS : MeasurableSet S := e.measurableEmbedding.measurableSet_image'
    (MeasurableSet.univ.prod hD)
  have hFD : IsFundamentalDomain Γ S μG := by
    refine IsFundamentalDomain.mk' hS.nullMeasurableSet ?_
    intro x
    obtain ⟨p, rfl⟩ := E.surjective x
    obtain ⟨h, hh, hu⟩ := fundamentalDomain_unique H hHdisc p.2
    have hmem (k : H) : E (1, (k : N)) * E p ∈ S ↔ (k : N) * p.2 ∈ D := by
      rw [← map_mul E]
      change E ((1, (k : N)) * p) ∈ E '' (univ ×ˢ D) ↔ _
      rw [E.injective.mem_set_image, mem_prod]
      exact and_iff_right (mem_univ _)
    let γ : Γ := ⟨E (1, (h : N)), (hΓ _).mpr ⟨rfl, h.property⟩⟩
    refine ⟨γ, (hmem h).mpr hh, ?_⟩
    intro δ hδ
    have hδp := (hΓ (E.symm δ.val)).mp (by rw [E.apply_symm_apply]; exact δ.property)
    let k : H := ⟨(E.symm δ.val).2, hδp.2⟩
    have hk : E (1, (k : N)) = δ.val := by
      rw [← E.apply_symm_apply δ.val]
      exact congrArg E (Prod.ext hδp.1.symm rfl)
    have hkh : k = h := hu k ((hmem k).mp (hk.symm ▸ hδ))
    exact Subtype.ext (hk.symm.trans (congrArg (fun z : H => E (1, (z : N))) hkh))
  have hrestrict : μG.restrict S = Measure.map E ((μA.prod μN).restrict (univ ×ˢ D)) := by
    rw [← hE.map_eq]
    change ((μA.prod μN).map e).restrict (e '' (univ ×ˢ D)) = _
    rw [e.measurableEmbedding.restrict_map, e.injective.preimage_image]
    rfl
  let Q := productHomeomorph E H Γ hΓ
  have hQ : Measurable Q := measurable_productHomeomorph E H Γ hΓ e.symm.measurable
  have hcomp : Q ∘ mk Γ ∘ E = Prod.map id (mk H) := by
    funext p
    exact productHomeomorph_mk E H Γ hΓ p
  refine ⟨hQ, ?_⟩
  rw [discreteQuotientMeasure_eq Γ hΓdisc μG hFD, quotientMeasure, hrestrict,
    Measure.map_map (measurable_mk Γ) hE.measurable,
    Measure.map_map hQ ((measurable_mk Γ).comp hE.measurable), hcomp]
  rw [← Measure.prod_restrict, ← Measure.map_prod_map _ _ measurable_id (measurable_mk H),
    Measure.map_id, Measure.restrict_univ]
  rfl

end Langlands.Global.LeftCosetSpace
