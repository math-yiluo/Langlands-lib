import Langlands.Representation.Hecke.IntegratedAction
import Langlands.Representation.Hecke.Convolution
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Algebra.NonUnitalHom

/-! Multiplicativity of the actual integrated Hecke action. -/

noncomputable section

namespace Langlands.Hecke

open HarmonicAnalysis MeasureTheory MeasureTheory.Measure Set Function
open scoped Pointwise

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

omit [MeasurableSpace G] [BorelSpace G] in
/-- Scalarized convolution-action kernels have compact support in both variables.
The representation coefficient need not have compact support. -/
theorem actionKernel_hasCompactSupport (ρ : Representation ℂ G V)
    (f g : SchwartzBruhat G) (v : V) (L : V →ₗ[ℂ] ℂ) :
    HasCompactSupport (fun p : G × G =>
      (f p.2 * g (p.2⁻¹ * p.1)) * L (ρ p.1 v)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (((TestFunction.isCompact_support f).mul (TestFunction.isCompact_support g)).prod
      (TestFunction.isCompact_support f))
  rintro ⟨z, y⟩ hp
  change (f y * g (y⁻¹ * z)) * L (ρ z v) ≠ 0 at hp
  have hfg := mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hp).1
  exact ⟨⟨y, hfg.1, y⁻¹ * z, hfg.2, by simp⟩, hfg.1⟩

/-- The finite-fiber integral action respects actual left-Haar convolution.
Scalarization and compact-support Fubini require no topology on the carrier and
no global sigma-finiteness hypothesis on Haar measure. -/
theorem integratedAction_convolution (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [IsMulLeftInvariant μ] (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (f g : SchwartzBruhat G) (v : V) :
    integratedAction μ ρ hρ (TestFunction.convolution μ f g) v =
      integratedAction μ ρ hρ f (integratedAction μ ρ hρ g v) := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
  intro L
  rw [map_sub, sub_eq_zero, integratedAction_dual, integratedAction_dual]
  change (∫ z, (∫ y, f y * g (y⁻¹ * z) ∂μ) * L (ρ z v) ∂μ) =
    ∫ y, f y * L (ρ y (integratedAction μ ρ hρ g v)) ∂μ
  calc
    _ = ∫ z, (∫ y, (f y * g (y⁻¹ * z)) * L (ρ z v) ∂μ) ∂μ := by
      congr 1
      funext z
      exact (integral_mul_const _ _).symm
    _ = ∫ y, (∫ z, (f y * g (y⁻¹ * z)) * L (ρ z v) ∂μ) ∂μ := by
      apply integral_integral_swap_of_hasCompactSupport
      · exact (f.continuous.comp continuous_snd |>.mul
          (g.continuous.comp (continuous_snd.inv.mul continuous_fst))).mul
          (((orbitMap_locallyConstant ρ (hρ v)).comp L).continuous.comp continuous_fst)
      · exact actionKernel_hasCompactSupport ρ f g v L
    _ = ∫ y, (∫ z, (f y * g z) * L (ρ y (ρ z v)) ∂μ) ∂μ := by
      congr 1
      funext y
      rw [← integral_mul_left_eq_self
        (fun z => (f y * g (y⁻¹ * z)) * L (ρ z v)) y]
      simp only [inv_mul_cancel_left, map_mul, Module.End.mul_apply]
    _ = _ := by
      congr 1
      funext y
      rw [show L (ρ y (integratedAction μ ρ hρ g v)) =
        ∫ z, g z * L (ρ y (ρ z v)) ∂μ from
          integratedAction_dual μ ρ hρ g v (L.comp (ρ y))]
      simp_rw [mul_assoc]
      exact integral_const_mul _ _

/-- The action of the actual measure-indexed nonunital Hecke algebra. Its
multiplication law is proved from integration, not assumed as structure data. -/
def heckeAction (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [IsMulLeftInvariant μ] (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) :
    HeckeAlgebra μ →ₙₐ[ℂ] Module.End ℂ V where
  toFun f := integratedAction μ ρ hρ (HeckeAlgebra.toTestFunction μ f)
  map_zero' := (integratedAction μ ρ hρ).map_zero
  map_add' f g := (integratedAction μ ρ hρ).map_add f g
  map_smul' c f := (integratedAction μ ρ hρ).map_smul c f
  map_mul' f g := by
    ext v
    exact integratedAction_convolution μ ρ hρ f g v

@[simp]
theorem heckeAction_apply (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [IsMulLeftInvariant μ] (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (f : HeckeAlgebra μ) (v : V) :
    heckeAction μ ρ hρ f v =
      integratedAction μ ρ hρ (HeckeAlgebra.toTestFunction μ f) v := rfl

/-- Left translation of the test function corresponds to the positive group
action on its integrated output. -/
theorem integratedAction_leftTranslate (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [IsMulLeftInvariant μ] (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (a : G) (f : SchwartzBruhat G) (v : V) :
    integratedAction μ ρ hρ (TestFunction.leftTranslate a f) v =
      ρ a (integratedAction μ ρ hρ f v) := by
  have heq :
      (actionIntegrand ρ hρ (TestFunction.leftTranslate a f) v).comp (a * ·)
        (measurePreserving_mul_left μ a).measurable =
      (actionIntegrand ρ hρ f v).map (ρ a) := by
    ext x
    simp [map_mul, Module.End.mul_apply]
  rw [integratedAction_apply, integratedAction_apply,
    ← AlgebraicIntegral.integral_comp_measurePreserving
      (actionIntegrand ρ hρ (TestFunction.leftTranslate a f) v) (a * ·)
      (measurePreserving_mul_left μ a), heq]
  exact AlgebraicIntegral.integral_linearMap _
    (actionIntegrand_finMeasSupp μ ρ hρ f v) (ρ a)

/-- Bi-invariance on the left forces the image of the integrated operator into
the existing fixed-vector submodule. -/
theorem integratedAction_mem_fixedVectors (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [IsMulLeftInvariant μ] (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    {K J : Subgroup G} {f : SchwartzBruhat G}
    (hf : f ∈ TestFunction.biInvariant K J) (v : V) :
    integratedAction μ ρ hρ f v ∈ fixedVectors ρ K := by
  change ∀ k : K, ρ (k : G) (integratedAction μ ρ hρ f v) =
    integratedAction μ ρ hρ f v
  intro k
  rw [← integratedAction_leftTranslate μ ρ hρ (k : G) f v,
    ((TestFunction.mem_biInvariant_iff K J f).mp hf).1 k]

/-- The unnormalized subgroup indicator acts on fixed vectors by its measure. -/
theorem integratedAction_subgroupIndicator_of_fixed
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) {v : V}
    (hv : v ∈ fixedVectors ρ K.toSubgroup) :
    integratedAction μ ρ hρ (TestFunction.subgroupIndicator K hK) v =
      ((μ (K : Set G)).toReal : ℂ) • v := by
  have heq : actionIntegrand ρ hρ (TestFunction.subgroupIndicator K hK) v =
      (SimpleFunc.const G v).restrict (K : Set G) := by
    ext x
    rw [SimpleFunc.restrict_apply _ K.isOpen.measurableSet]
    by_cases hx : x ∈ K
    · have hfix : ρ x v = v := hv ⟨x, hx⟩
      simp [TestFunction.subgroupIndicator_apply, hx, hfix]
    · simp [TestFunction.subgroupIndicator_apply, hx]
  rw [integratedAction_apply, heq]
  exact AlgebraicIntegral.integral_indicator_const _ K.isOpen.measurableSet v

end Langlands.Hecke
