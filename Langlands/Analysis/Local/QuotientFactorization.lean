import Langlands.Analysis.Local.QuotientAutomorphismProof
import Mathlib.MeasureTheory.Integral.Prod

/-! # Actual left-quotient charts from an ordered product factorization -/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure
open scoped CompactlySupported

universe uG uX

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Subgroup G) {X : Type uX} [TopologicalSpace X]
variable (s : X → G) (m : H × X ≃ₜ G)
variable (hm : ∀ p : H × X, m p = p.1.val * s p.2)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem quotient_mk_factor (h : H) (g : G) :
    Quotient.mk (QuotientGroup.rightRel H) (h.val * g) =
      Quotient.mk (QuotientGroup.rightRel H) g := by
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  simp [mul_inv_rev]

include hm in
/-- Literal ordered multiplication coordinates descend to a homeomorphism
onto the actual left quotient; the coordinate space need not be a group. -/
theorem isHomeomorph_factorQuotient :
    IsHomeomorph (fun x : X => (Quotient.mk _ (s x) : LeftQuotient H)) := by
  have hs : Continuous s := by
    have hc := m.continuous.comp (continuous_const.prodMk continuous_id :
      Continuous (fun x : X => ((1 : H), x)))
    simpa only [Function.comp_def, hm, OneMemClass.coe_one, one_mul] using hc
  have hcomm : (leftQuotientMap H) ∘ m =
      (fun x : X => (Quotient.mk _ (s x) : LeftQuotient H)) ∘ Prod.snd := by
    funext p
    simp only [Function.comp_apply, leftQuotientMap_apply, hm, quotient_mk_factor]
  refine ⟨continuous_quotient_mk'.comp hs, ?_, ?_, ?_⟩
  · apply IsOpenMap.of_comp continuous_snd (fun x => ⟨((1 : H), x), rfl⟩)
    rw [← hcomm]
    exact (leftQuotient_isOpenQuotientMap H).isOpenMap.comp m.isOpenMap
  · intro x y hxy
    let h : H := ⟨s y * (s x)⁻¹,
      QuotientGroup.rightRel_apply.mp (Quotient.exact hxy)⟩
    have heq : m ((1 : H), y) = m (h, x) := by
      simp only [hm, OneMemClass.coe_one, one_mul, h]
      simp [mul_assoc]
    exact (congrArg Prod.snd (m.injective heq)).symm
  · intro q
    induction q using Quotient.inductionOn with
    | h g =>
      obtain ⟨p, rfl⟩ := m.surjective g
      exact ⟨p.2, by rw [hm, quotient_mk_factor]⟩

/-- The concrete quotient chart induced by `(h,x) ↦ h * s(x)`. -/
def factorQuotientHomeomorph : X ≃ₜ LeftQuotient H :=
  IsHomeomorph.homeomorph _ (isHomeomorph_factorQuotient H s m hm)

@[simp] theorem factorQuotientHomeomorph_apply (x : X) :
    factorQuotientHomeomorph H s m hm x = Quotient.mk _ (s x) := rfl

/-- The inverse chart reads the second ordered factor of any representative. -/
@[simp] theorem factorQuotientHomeomorph_symm_mk (g : G) :
    (factorQuotientHomeomorph H s m hm).symm (Quotient.mk _ g) =
      (m.symm g).2 := by
  apply (factorQuotientHomeomorph H s m hm).injective
  rw [Homeomorph.apply_symm_apply, factorQuotientHomeomorph_apply]
  have hg := m.apply_symm_apply g
  rw [hm] at hg
  calc
    (Quotient.mk _ g : LeftQuotient H) =
        Quotient.mk _ ((m.symm g).1.val * s (m.symm g).2) :=
      congrArg (Quotient.mk _) hg.symm
    _ = _ := quotient_mk_factor H _ _

section Measures

variable [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (hH : IsClosed (H : Set G)) [MeasurableSpace H] [BorelSpace H]
variable [MeasurableSpace X] [BorelSpace X]
variable {μG : Measure G} {μH : Measure H} {μX : Measure X}
variable [IsFiniteMeasureOnCompacts μG]
variable [IsHaarMeasure μH] [μH.Regular] [IsMulRightInvariant μH]
variable [SFinite μH] [SFinite μX] [μX.Regular]
variable [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
variable {ν : Measure (LeftQuotient H)}

include hH in
/-- Exact product normalization descends to any supplied compatible quotient
measure. No quotient-chart measure comparison is assumed. -/
theorem IsCompatible.measurePreserving_factorQuotientHomeomorph
    (hν : IsCompatible H μG μH ν)
    (hprod : MeasurePreserving m (μH.prod μX) μG) :
    MeasurePreserving (factorQuotientHomeomorph H s m hm) μX ν := by
  let c := factorQuotientHomeomorph H s m hm
  have : T2Space (LeftQuotient H) := leftQuotient_t2Space H hH
  have : LocallyCompactSpace (LeftQuotient H) := leftQuotient_locallyCompactSpace H
  have : ν.Regular := hν.regular
  have : (Measure.map c μX).Regular := Measure.Regular.map c
  refine ⟨c.continuous.measurable, ?_⟩
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  obtain ⟨f, hf, -⟩ := realQuotientPositiveLifting H hH μH φ
  have hfi : Integrable f μG :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hfprod : Integrable (fun p : H × X => f (m p)) (μH.prod μX) :=
    hprod.integrable_comp_of_integrable hfi
  have hmap : (∫ g, f g ∂μG) = ∫ p : H × X, f (m p) ∂μH.prod μX := by
    have hfm : AEStronglyMeasurable f (Measure.map m (μH.prod μX)) := by
      rw [hprod.map_eq]
      exact hfi.aestronglyMeasurable
    have hi := integral_map hprod.measurable.aemeasurable hfm
    rwa [hprod.map_eq] at hi
  calc
    (∫ q, φ q ∂Measure.map c μX) = ∫ x, φ (c x) ∂μX :=
      integral_map_equiv c.toMeasurableEquiv φ
    _ = ∫ x, ∫ h : H, f (m (h, x)) ∂μH ∂μX := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        simpa only [c, factorQuotientHomeomorph_apply, hm] using (hf (s x)).symm)
    _ = ∫ p : H × X, f (m p) ∂μH.prod μX :=
      (integral_prod_symm _ hfprod).symm
    _ = ∫ g, f g ∂μG := hmap.symm
    _ = ∫ q, quotientAverageReal H μH f q ∂ν :=
      (hν.integral_quotientAverageReal f f.continuous f.hasCompactSupport).symm
    _ = ∫ q, φ q ∂ν := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro q
      induction q using Quotient.inductionOn with
      | h g => exact hf g

end Measures

end Langlands.QuotientIntegration
