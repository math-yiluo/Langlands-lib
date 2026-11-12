import Langlands.Representation.Hecke.CompactInductionComparison

/-! Scalarization and the module laws for the III.2.6 comparison. -/

noncomputable section

open MeasureTheory CategoryTheory MulOpposite

namespace Langlands.Hecke.Homomorphism

open HarmonicAnalysis

universe uG v

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  (H : Subgroup G) [LocallyCompactSpace H] (hH : IsClosed (H : Set G))
  (μH : Measure H) [μH.IsHaarMeasure]
  {V : Type v} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ H V) (hρ : IsSmooth ρ)

/-- Scalarizing the subgroup-action integrand produces a genuine test function,
although the representation coefficient itself need not have compact support. -/
def compactComparisonScalarTest (T : SchwartzBruhat G) (w : V) (g : G)
    (ell : V →ₗ[ℂ] ℂ) : SchwartzBruhat H :=
  ⟨fun h => compactSubgroupTest H hH g T h * ell (ρ h w),
    (compactSubgroupTest H hH g T).locallyConstant.mul
      ((orbitMap_locallyConstant ρ (hρ w)).comp ell),
    (compactSubgroupTest H hH g T).hasCompactSupport.mul_right⟩

/-- The elementary comparison has exactly Renard's scalarized integral formula. -/
theorem compactComparisonValue_dual (T : SchwartzBruhat G) (w : V) (g : G)
    (ell : V →ₗ[ℂ] ℂ) :
    ell (compactComparisonValue H hH μH ρ hρ T w g) =
      ∫ h : H, T (((h : G) * g)⁻¹) * haarScale (h : G) *
        ell (ρ h⁻¹ w) ∂μH := by
  rw [compactComparisonValue, integratedAction_dual]
  let s := compactComparisonScalarTest H hH ρ hρ T w g ell
  change (∫ h, s h ∂μH) = _
  rw [← integral_haarInversion μH s]
  apply integral_congr_ae
  filter_upwards [] with h
  change haarScale h *
    ((haarScale h⁻¹ * haarScale (((h⁻¹)⁻¹ : H) : G)) *
      T (g⁻¹ * ((h⁻¹ : H) : G)) * ell (ρ h⁻¹ w)) = _
  simp only [inv_inv, Subgroup.coe_inv, mul_inv_rev]
  calc
    _ = (haarScale h * haarScale h⁻¹) *
        (T (g⁻¹ * (h : G)⁻¹) * haarScale (h : G) * ell (ρ h⁻¹ w)) := by ring
    _ = _ := by rw [haarScale_mul_inverse, one_mul]


variable (μG : Measure G) [μG.IsHaarMeasure]

/-- Restriction with the relative modular weight converts the original right
Hecke action into subgroup convolution. -/
theorem compactSubgroupTest_rightModule (g : G) (T : HeckeAlgebra μG)
    (a : HeckeAlgebra μH) :
    (letI := rightModule μG μH H.subtype continuous_subtype_val
     compactSubgroupTest H hH g (op a • T)) =
      TestFunction.convolution μH (compactSubgroupTest H hH g T) a := by
  ext t
  let b := rightConvolutionKernel μG μH H.subtype continuous_subtype_val a T
    (g⁻¹ * (t : G))
  let χ := (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom
  change (χ t : ℂ) *
    (letI := rightModule μG μH H.subtype continuous_subtype_val
     (op a • T) (g⁻¹ * (t : G))) =
      ∫ s, compactSubgroupTest H hH g T s * a (s⁻¹ * t) ∂μH
  rw [rightModule_integral μG μH H.subtype continuous_subtype_val]
  change (χ t : ℂ) * (∫ k, b k ∂μH) = _
  rw [← integral_haarInversion μH b, ← integral_const_mul]
  rw [← integral_mul_left_eq_self
    (fun s => compactSubgroupTest H hH g T s * a (s⁻¹ * t)) t]
  apply integral_congr_ae
  filter_upwards [] with k
  change (χ t : ℂ) * (haarScale k *
      (haarScale ((k⁻¹ : H) : G) * a k⁻¹ *
        T ((g⁻¹ * (t : G)) * (((k⁻¹ : H) : G))⁻¹))) =
    (χ (t * k) : ℂ) * T (g⁻¹ * ((t * k : H) : G)) * a ((t * k)⁻¹ * t)
  rw [map_mul, Units.val_mul]
  rw [show (χ k : ℂ) = haarScale k * haarScale ((k⁻¹ : H) : G) from rfl]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv,
    inv_inv, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  ring

/-- The elementary comparison is balanced for the actual subgroup Hecke action. -/
theorem compactComparisonFunction_balanced (T : HeckeAlgebra μG)
    (a : HeckeAlgebra μH) (w : V) :
    (letI := rightModule μG μH H.subtype continuous_subtype_val
     compactComparisonFunction H hH μH ρ hρ (op a • T) w) =
      compactComparisonFunction H hH μH ρ hρ T
        (integratedAction μH ρ hρ a w) := by
  ext g
  change integratedAction μH ρ hρ
    (letI := rightModule μG μH H.subtype continuous_subtype_val
     compactSubgroupTest H hH g (op a • T)) w = _
  rw [compactSubgroupTest_rightModule H hH μH μG]
  exact integratedAction_convolution μH ρ hρ (compactSubgroupTest H hH g T) a w

/-- Left translation on ambient test functions becomes right translation of
compact induced functions. -/
theorem compactComparisonFunction_leftTests (x : G) (T : SchwartzBruhat G) (w : V) :
    compactComparisonFunction H hH μH ρ hρ (GroupAction.leftTests x T) w =
      Induction.compactInduced H
        (Langlands.twist
          (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom ρ) x
        (compactComparisonFunction H hH μH ρ hρ T w) := by
  ext g
  change integratedAction μH ρ hρ
    (compactSubgroupTest H hH g (GroupAction.leftTests x T)) w =
      integratedAction μH ρ hρ (compactSubgroupTest H hH (g * x) T) w
  congr 2
  ext h
  simp only [compactSubgroupTest_apply, GroupAction.leftTests_apply, mul_inv_rev, mul_assoc]

/-- For fixed w the elementary map intertwines the ambient group actions. -/
def compactComparisonIntertwiner (w : V) :
    (GroupAction.leftTests (G := G)).IntertwiningMap
      (Induction.compactInduced H
        (Langlands.twist
          (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom ρ)) where
  toLinearMap :=
    { toFun := fun T => compactComparisonBilinear H hH μH ρ hρ T w
      map_add' := fun T S => congrArg (fun f : V →ₗ[ℂ] _ => f w)
        ((compactComparisonBilinear H hH μH ρ hρ).map_add T S)
      map_smul' := fun c T => congrArg (fun f : V →ₗ[ℂ] _ => f w)
        ((compactComparisonBilinear H hH μH ρ hρ).map_smul c T) }
  isIntertwining' x := by
    apply LinearMap.ext
    intro T
    exact compactComparisonFunction_leftTests H hH μH ρ hρ x T w

/-- Integrating the left regular action is the original Haar convolution. -/
theorem integratedAction_leftTests (a T : HeckeAlgebra μG) :
    integratedAction μG (GroupAction.leftTests (G := G)) isSmooth_leftTests a T = a * T := by
  ext x
  exact leftModule_apply μG μG (MonoidHom.id G) continuous_id a T x

/-- The elementary comparison respects the original ambient Hecke action. -/
theorem compactComparisonFunction_hecke (a T : HeckeAlgebra μG) (w : V) :
    compactComparisonFunction H hH μH ρ hρ (a * T) w =
      integratedAction μG
        (Induction.compactInduced H
          (Langlands.twist
            (relativeModularCharacter H.subtype continuous_subtype_val).toMonoidHom ρ))
        (Induction.compactInduced_smooth H _) a
        (compactComparisonFunction H hH μH ρ hρ T w) := by
  rw [← integratedAction_leftTests μG]
  exact integratedAction_intertwiner μG isSmooth_leftTests
    (Induction.compactInduced_smooth H _)
    (compactComparisonIntertwiner H hH μH ρ hρ w) a T

end Langlands.Hecke.Homomorphism
