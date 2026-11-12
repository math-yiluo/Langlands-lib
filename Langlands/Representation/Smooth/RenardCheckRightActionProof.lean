import Langlands.Representation.Smooth.RenardCoinvariantTensorStatements

noncomputable section

open MeasureTheory MeasureTheory.Measure MulOpposite

namespace Langlands.Renard.Smooth

open Langlands.Hecke Langlands.Algebra Langlands.HarmonicAnalysis

universe u v

namespace CheckAction

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
  (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

/-- The integrated inverse-action operator, linear in the test function. -/
def operator : SchwartzBruhat G →ₗ[ℂ] Module.End ℂ V :=
  (integratedAction μ.inv ρ hρ).comp TestFunction.inversion.toLinearMap

/-- Scalar evaluation of the inverse-action operator uses the original left measure. -/
theorem dual (f : SchwartzBruhat G) (v : V) (L : V →ₗ[ℂ] ℂ) :
    L (operator μ ρ hρ f v) = ∫ g, f g * L (ρ g⁻¹ v) ∂μ := by
  rw [operator, LinearMap.comp_apply, integratedAction_dual]
  change (∫ g, TestFunction.inversion f g * L (ρ g v)
    ∂Measure.map (MeasurableEquiv.inv G) μ) = _
  rw [integral_map_equiv]
  simp only [MeasurableEquiv.inv_apply, TestFunction.inversion_apply, inv_inv]

variable [IsMulLeftInvariant μ]

/-- Left-Haar convolution acts in reverse order under the inverse action. -/
theorem convolution (f g : SchwartzBruhat G) (v : V) :
    operator μ ρ hρ (TestFunction.convolution μ f g) v =
      operator μ ρ hρ g (operator μ ρ hρ f v) := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro L
  rw [map_sub, sub_eq_zero, dual]
  change (∫ z, (∫ y, f y * g (y⁻¹ * z) ∂μ) * L (ρ z⁻¹ v) ∂μ) = _
  calc
    _ = ∫ z, (∫ y, (f y * g (y⁻¹ * z)) * L (ρ z⁻¹ v) ∂μ) ∂μ := by
      congr 1
      funext z
      exact (integral_mul_const _ _).symm
    _ = ∫ y, (∫ z, (f y * g (y⁻¹ * z)) * L (ρ z⁻¹ v) ∂μ) ∂μ := by
      apply integral_integral_swap_of_hasCompactSupport
      · exact (f.continuous.comp continuous_snd |>.mul
          (g.continuous.comp (continuous_snd.inv.mul continuous_fst))).mul
          (((orbitMap_locallyConstant ρ (hρ v)).comp L).continuous.comp continuous_fst.inv)
      · apply HasCompactSupport.of_support_subset_isCompact
          (((TestFunction.isCompact_support f).mul (TestFunction.isCompact_support g)).prod
            (TestFunction.isCompact_support f))
        rintro ⟨z, y⟩ hp
        change (f y * g (y⁻¹ * z)) * L (ρ z⁻¹ v) ≠ 0 at hp
        have hfg := mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hp).1
        exact ⟨⟨y, hfg.1, y⁻¹ * z, hfg.2, by simp⟩, hfg.1⟩
    _ = ∫ y, (∫ z, (f y * g z) * L (ρ z⁻¹ (ρ y⁻¹ v)) ∂μ) ∂μ := by
      congr 1
      funext y
      rw [← integral_mul_left_eq_self
        (fun z => (f y * g (y⁻¹ * z)) * L (ρ z⁻¹ v)) y]
      simp only [inv_mul_cancel_left, mul_inv_rev, map_mul, Module.End.mul_apply]
    _ = ∫ y, f y * L (operator μ ρ hρ g (ρ y⁻¹ v)) ∂μ := by
      congr 1
      funext y
      rw [dual]
      simp_rw [mul_assoc]
      exact integral_const_mul _ _
    _ = L (operator μ ρ hρ g (operator μ ρ hρ f v)) :=
      (dual μ ρ hρ f v (L.comp (operator μ ρ hρ g))).symm

/-- The opposite Hecke algebra acts by the integrated inverse action. -/
abbrev module : NonUnitalModule (HeckeAlgebra μ)ᵐᵒᵖ V where
  smul f v := operator μ ρ hρ (HeckeAlgebra.toTestFunction μ (unop f)) v
  smul_zero f := map_zero _
  smul_add f := map_add _
  mul_smul f g v := convolution μ ρ hρ _ _ v
  add_smul f g v := by
    change operator μ ρ hρ (HeckeAlgebra.toTestFunction μ (unop f) +
      HeckeAlgebra.toTestFunction μ (unop g)) v = _
    exact congrArg (fun T : Module.End ℂ V => T v) ((operator μ ρ hρ).map_add _ _)
  zero_smul v := by
    change operator μ ρ hρ 0 v = 0
    rw [map_zero, LinearMap.zero_apply]

end CheckAction

/-- Renard III.1.15: the check operators give the required right Hecke action. -/
theorem checkRightActionExists : CheckRightActionExistsStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ μ _ V _ _ ρ hρ
  exact ⟨CheckAction.module μ ρ hρ, fun _ _ => rfl⟩

end Langlands.Renard.Smooth
