import Langlands.Representation.Hecke.CompactInductionRightFormula
import Langlands.Representation.Hecke.ActionLocalUnits

/-! # Group balancing in the original Hecke tensor -/

noncomputable section

open MeasureTheory MulOpposite

namespace Langlands.Hecke

open HarmonicAnalysis Langlands.Algebra

universe uG uH v

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (μG : Measure G) [μG.IsHaarMeasure]

omit [T2Space G] [BorelSpace G] [μG.IsHaarMeasure] in
/-- The original Haar-distribution inversion fixes compact-open averaging tests. -/
theorem haarInversion_normalizedIndicator (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) :
    haarInversion μG (HeckeAlgebra.normalizedIndicator μG K hK) =
      HeckeAlgebra.normalizedIndicator μG K hK := by
  ext x
  change haarScale x * HeckeAlgebra.normalizedIndicator μG K hK x⁻¹ =
    HeckeAlgebra.normalizedIndicator μG K hK x
  by_cases hx : x ∈ K
  · have hxinv : x⁻¹ ∈ K := K.inv_mem hx
    have hχ : haarScale x = 1 := by
      simp [haarScale, Haar.modularCharacter_eq_one_of_mem_compactOpen K hK hx]
    simp [HeckeAlgebra.normalizedIndicator_apply, hx, hxinv, hχ]
  · have hxinv : x⁻¹ ∉ K := by
      intro hi
      apply hx
      change x ∈ K.toSubgroup
      simpa only [inv_inv] using K.toSubgroup.inv_mem hi
    simp [HeckeAlgebra.normalizedIndicator_apply, hx, hxinv]

/-- Left translation on the Hecke-algebra type synonym, retaining its module instances. -/
def HeckeAlgebra.leftTranslated (g : G) : HeckeAlgebra μG ≃ₗ[ℂ] HeckeAlgebra μG :=
  (HeckeAlgebra.toTestFunction μG).trans
    ((TestFunction.leftTranslate g).trans (HeckeAlgebra.toTestFunction μG).symm)

omit [T2Space G] [LocallyCompactSpace G] in
@[simp] theorem HeckeAlgebra.leftTranslated_apply (g : G) (a : HeckeAlgebra μG) (x : G) :
    HeckeAlgebra.leftTranslated μG g a x = a (g⁻¹ * x) := rfl

namespace Homomorphism

variable {H : Type uH} [Group H] [TopologicalSpace H] [T2Space H]
  [NonarchimedeanGroup H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
  (μH : Measure H) [μH.IsHaarMeasure]
  (φ : H →* G) (hφ : Continuous φ)

/-- Left translation of a subgroup test moves its group action to the first
factor, with the inverse required by a right action. -/
theorem rightModule_leftTranslate (h : H) (a : HeckeAlgebra μH)
    (T : HeckeAlgebra μG) :
    (letI := rightModule μG μH φ hφ
     op (HeckeAlgebra.leftTranslated μH h a) • T) =
      (letI := rightModule μG μH φ hφ
       op a • (rightRepresentation μG φ h⁻¹ T)) := by
  ext x
  rw [rightModule_integral, rightModule_integral]
  rw [← integral_mul_left_eq_self (μ := μH)
    (fun t => haarScale (φ t) * HeckeAlgebra.leftTranslated μH h a t *
      T (x * (φ t)⁻¹)) h]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [HeckeAlgebra.leftTranslated_apply, inv_mul_cancel_left,
    rightRepresentation_apply, map_mul, map_inv, mul_inv_rev, inv_inv, mul_assoc]
  ring

variable {V : Type v} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ H V) (hρ : IsSmooth ρ)

/-- The original balancing quotient is also balanced for individual group
elements, as a consequence of smooth local units and the Hecke balancing law. -/
theorem tensor_group_balanced (h : H) (T : HeckeAlgebra μG) (w : V) :
    letI := rightModule μG μH φ hφ
    letI := heckeNonUnitalModule μH ρ hρ
    NonUnitalModuleTensor.tmul (HeckeAlgebra μH) (HeckeAlgebra μG) V
        (rightRepresentation μG φ h⁻¹ T) w =
      NonUnitalModuleTensor.tmul (HeckeAlgebra μH) (HeckeAlgebra μG) V T (ρ h w) := by
  let _ := rightModule μG μH φ hφ
  let _ := heckeNonUnitalModule μH ρ hρ
  obtain ⟨U, hU⟩ := rightRepresentation_isSmooth μG φ hφ
    (rightRepresentation μG φ h⁻¹ T)
  obtain ⟨J, hJ⟩ := hρ w
  obtain ⟨K, hKUJ, hK, _⟩ :=
    TestFunction.commonCompactOpenBiInvariance H ∅ (U ⊓ J)
  let e := HeckeAlgebra.normalizedIndicator μH K hK
  have heT : op e • (rightRepresentation μG φ h⁻¹ T) =
      rightRepresentation μG φ h⁻¹ T := by
    rw [rightModule_eq_integrated, haarInversion_normalizedIndicator]
    apply heckeAction_normalizedIndicator_of_fixed
    intro k
    exact hU ⟨k, (hKUJ k.property).1⟩
  have hew : heckeAction μH ρ hρ e w = w := by
    apply heckeAction_normalizedIndicator_of_fixed
    intro k
    exact hJ ⟨k, (hKUJ k.property).2⟩
  have hhw : HeckeAlgebra.leftTranslated μH h e • w = ρ h w := by
    change integratedAction μH ρ hρ
      (TestFunction.leftTranslate h (HeckeAlgebra.toTestFunction μH e)) w = _
    exact (integratedAction_leftTranslate μH ρ hρ h
      (HeckeAlgebra.toTestFunction μH e) w).trans (congrArg (ρ h) hew)
  calc
    _ = NonUnitalModuleTensor.tmul (HeckeAlgebra μH) (HeckeAlgebra μG) V
        (op e • (rightRepresentation μG φ h⁻¹ T)) w := by rw [heT]
    _ = NonUnitalModuleTensor.tmul (HeckeAlgebra μH) (HeckeAlgebra μG) V
        (op (HeckeAlgebra.leftTranslated μH h e) • T) w := by
      rw [rightModule_leftTranslate]
    _ = NonUnitalModuleTensor.tmul (HeckeAlgebra μH) (HeckeAlgebra μG) V T
        (HeckeAlgebra.leftTranslated μH h e • w) :=
      NonUnitalModuleTensor.tmul_balanced _ _ _ _ _ _
    _ = _ := by rw [hhw]

end Homomorphism

end Langlands.Hecke
