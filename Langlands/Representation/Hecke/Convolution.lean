import Langlands.Representation.Hecke.TestFunction
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral

/-! # Left-Haar convolution of actual Hecke test functions -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Function Filter
open scoped Topology Pointwise

namespace Langlands.Hecke

universe u

open HarmonicAnalysis (SchwartzBruhat)

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

/-- Left-Haar convolution, with the convention `f(y) g(y⁻¹x)`.
For arbitrary functions this uses the usual Bochner integral convention. -/
def convolutionIntegral (μ : Measure G) (f g : G → ℂ) (x : G) : ℂ :=
  ∫ y, f y * g (y⁻¹ * x) ∂μ

namespace TestFunction

variable (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

/-- Every convolution integral of test functions is integrable. -/
theorem convolutionIntegrand_integrable (f g : SchwartzBruhat G) (x : G) :
    Integrable (fun y => f y * g (y⁻¹ * x)) μ := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact f.continuous.mul (g.continuous.comp (continuous_inv.mul continuous_const))
  · exact f.hasCompactSupport.mul_right

omit [BorelSpace G] [IsFiniteMeasureOnCompacts μ] in
/-- A compact tube argument proves local constancy without choosing a subgroup. -/
theorem convolutionIntegral_locallyConstant (f g : SchwartzBruhat G) :
    IsLocallyConstant (convolutionIntegral μ f g) := by
  classical
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  have he : ∀ᶠ z in 𝓝 x, ∀ y ∈ support (f : G → ℂ),
      g (y⁻¹ * z) = g (y⁻¹ * x) := by
    apply (isCompact_support f).eventually_forall_of_forall_eventually
    intro y _
    have h₁ : IsLocallyConstant (fun p : G × G => g (p.2⁻¹ * p.1)) :=
      g.locallyConstant.comp_continuous (continuous_snd.inv.mul continuous_fst)
    have h₂ : IsLocallyConstant (fun p : G × G => g (p.2⁻¹ * x)) :=
      g.locallyConstant.comp_continuous (continuous_snd.inv.mul continuous_const)
    filter_upwards [h₁.eventually_eq (x, y), h₂.eventually_eq (x, y)] with p hp hq
    exact hp.trans hq.symm
  filter_upwards [he] with z hz
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    by_cases hy : f y = 0
    · simp [hy]
    · exact congrArg (f y * ·) (hz y hy)

omit [IsTopologicalGroup G] [BorelSpace G] [IsFiniteMeasureOnCompacts μ] in
/-- The support of convolution is contained in the product of the actual supports. -/
theorem support_convolutionIntegral_subset (f g : SchwartzBruhat G) :
    support (convolutionIntegral μ f g) ⊆ support (f : G → ℂ) * support (g : G → ℂ) := by
  classical
  intro x hx
  by_contra h
  apply hx
  apply integral_eq_zero_of_ae
  exact Eventually.of_forall fun y => by
    by_cases hf : f y = 0
    · simp [hf]
    · have hg : g (y⁻¹ * x) = 0 := by
        by_contra hg
        exact h ⟨y, hf, y⁻¹ * x, hg, by simp⟩
      simp [hg]

omit [BorelSpace G] [IsFiniteMeasureOnCompacts μ] in
/-- Convolution preserves compact support. -/
theorem convolutionIntegral_hasCompactSupport (f g : SchwartzBruhat G) :
    HasCompactSupport (convolutionIntegral μ f g) :=
  HasCompactSupport.of_support_subset_isCompact
    ((isCompact_support f).mul (isCompact_support g))
    (support_convolutionIntegral_subset μ f g)

/-- The actual convolution product on compactly supported locally constant functions. -/
def convolution (f g : SchwartzBruhat G) : SchwartzBruhat G :=
  ⟨convolutionIntegral μ f g, convolutionIntegral_locallyConstant μ f g,
    convolutionIntegral_hasCompactSupport μ f g⟩

omit [BorelSpace G] [IsFiniteMeasureOnCompacts μ] in
@[simp] theorem convolution_apply (f g : SchwartzBruhat G) (x : G) :
    convolution μ f g x = ∫ y, f y * g (y⁻¹ * x) ∂μ := rfl

theorem convolution_add_left (f₁ f₂ g : SchwartzBruhat G) :
    convolution μ (f₁ + f₂) g = convolution μ f₁ g + convolution μ f₂ g := by
  ext x
  change (∫ y, (f₁ y + f₂ y) * g (y⁻¹ * x) ∂μ) = _
  simp_rw [add_mul]
  exact integral_add (convolutionIntegrand_integrable μ f₁ g x)
    (convolutionIntegrand_integrable μ f₂ g x)

theorem convolution_add_right (f g₁ g₂ : SchwartzBruhat G) :
    convolution μ f (g₁ + g₂) = convolution μ f g₁ + convolution μ f g₂ := by
  ext x
  change (∫ y, f y * (g₁ (y⁻¹ * x) + g₂ (y⁻¹ * x)) ∂μ) = _
  simp_rw [mul_add]
  exact integral_add (convolutionIntegrand_integrable μ f g₁ x)
    (convolutionIntegrand_integrable μ f g₂ x)

omit [BorelSpace G] [IsFiniteMeasureOnCompacts μ] in
theorem convolution_smul_left (c : ℂ) (f g : SchwartzBruhat G) :
    convolution μ (c • f) g = c • convolution μ f g := by
  ext x
  change (∫ y, (c * f y) * g (y⁻¹ * x) ∂μ) = c * _
  simp_rw [mul_assoc]
  exact integral_const_mul c _

omit [BorelSpace G] [IsFiniteMeasureOnCompacts μ] in
theorem convolution_smul_right (c : ℂ) (f g : SchwartzBruhat G) :
    convolution μ f (c • g) = c • convolution μ f g := by
  ext x
  change (∫ y, f y * (c * g (y⁻¹ * x)) ∂μ) = c * _
  simp_rw [mul_left_comm (f _) c]
  exact integral_const_mul c _

/-- Convolution as a complex bilinear map, derived from its actual integral. -/
def convolutionBilinear : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat G where
  toFun f :=
    { toFun := convolution μ f
      map_add' := convolution_add_right μ f
      map_smul' := fun c g => convolution_smul_right μ c f g }
  map_add' f₁ f₂ := by
    ext g x
    exact congrArg (fun h : SchwartzBruhat G => h x) (convolution_add_left μ f₁ f₂ g)
  map_smul' c f := by
    ext g x
    exact congrArg (fun h : SchwartzBruhat G => h x) (convolution_smul_left μ c f g)

omit [MeasurableSpace G] [BorelSpace G] in
/-- The compactly supported double kernel used in associativity. -/
theorem associativityKernel_hasCompactSupport (f g h : SchwartzBruhat G) (x : G) :
    HasCompactSupport (fun p : G × G =>
      (f p.2 * g (p.2⁻¹ * p.1)) * h (p.1⁻¹ * x)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (((isCompact_support f).mul (isCompact_support g)).prod (isCompact_support f))
  rintro ⟨z, y⟩ hp
  change (f y * g (y⁻¹ * z)) * h (z⁻¹ * x) ≠ 0 at hp
  have hfg := mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hp).1
  exact ⟨⟨y, hfg.1, y⁻¹ * z, hfg.2, by simp⟩, hfg.1⟩

/-- Associativity follows from compact-support Fubini and left-Haar substitution.
No global sigma-finiteness or right-invariance hypothesis is used. -/
theorem convolution_assoc [IsMulLeftInvariant μ] (f g h : SchwartzBruhat G) :
    convolution μ (convolution μ f g) h = convolution μ f (convolution μ g h) := by
  ext x
  change (∫ z, (∫ y, f y * g (y⁻¹ * z) ∂μ) * h (z⁻¹ * x) ∂μ) =
    ∫ y, f y * (∫ z, g z * h (z⁻¹ * (y⁻¹ * x)) ∂μ) ∂μ
  calc
    _ = ∫ z, (∫ y, (f y * g (y⁻¹ * z)) * h (z⁻¹ * x) ∂μ) ∂μ := by
      congr 1
      funext z
      exact (integral_mul_const _ _).symm
    _ = ∫ y, (∫ z, (f y * g (y⁻¹ * z)) * h (z⁻¹ * x) ∂μ) ∂μ := by
      apply integral_integral_swap_of_hasCompactSupport
      · exact (f.continuous.comp continuous_snd |>.mul
          (g.continuous.comp (continuous_snd.inv.mul continuous_fst))).mul
          (h.continuous.comp (continuous_fst.inv.mul continuous_const))
      · exact associativityKernel_hasCompactSupport f g h x
    _ = ∫ y, (∫ z, (f y * g z) * h (z⁻¹ * (y⁻¹ * x)) ∂μ) ∂μ := by
      congr 1
      funext y
      rw [← integral_mul_left_eq_self
        (fun z => (f y * g (y⁻¹ * z)) * h (z⁻¹ * x)) y]
      simp only [inv_mul_cancel_left, mul_inv_rev, mul_assoc]
    _ = _ := by
      congr 1
      funext y
      simp_rw [mul_assoc]
      exact integral_const_mul _ _

end TestFunction

/-- The Hecke carrier with its Haar measure recorded as a type parameter.
This is exactly the existing test-function vector space, equipped below with convolution. -/
def HeckeAlgebra (_μ : Measure G) := SchwartzBruhat G

namespace HeckeAlgebra

variable (μ : Measure G)

instance : AddCommGroup (HeckeAlgebra μ) := inferInstanceAs (AddCommGroup (SchwartzBruhat G))
instance : Module ℂ (HeckeAlgebra μ) := inferInstanceAs (Module ℂ (SchwartzBruhat G))
instance : CoeFun (HeckeAlgebra μ) (fun _ => G → ℂ) := ⟨fun f => (show SchwartzBruhat G from f).val⟩

/-- The identity linear equivalence with the underlying actual test functions. -/
def toTestFunction : HeckeAlgebra μ ≃ₗ[ℂ] SchwartzBruhat G := LinearEquiv.refl ℂ _

omit [Group G] [IsTopologicalGroup G] [BorelSpace G] in
@[ext] theorem ext {f g : HeckeAlgebra μ} (h : ∀ x, f x = g x) : f = g :=
  TestFunction.ext h

instance : Mul (HeckeAlgebra μ) := ⟨TestFunction.convolution μ⟩

omit [BorelSpace G] in
@[simp] theorem mul_apply (f g : HeckeAlgebra μ) (x : G) :
    (f * g) x = ∫ y, f y * g (y⁻¹ * x) ∂μ := rfl

variable [IsFiniteMeasureOnCompacts μ] [IsMulLeftInvariant μ]

instance nonUnitalRing : NonUnitalRing (HeckeAlgebra μ) where
  toAddCommGroup := inferInstanceAs (AddCommGroup (SchwartzBruhat G))
  mul := TestFunction.convolution μ
  mul_assoc := TestFunction.convolution_assoc μ
  left_distrib := TestFunction.convolution_add_right μ
  right_distrib := TestFunction.convolution_add_left μ
  zero_mul f := by
    ext x
    change (∫ y, (0 : ℂ) * f (y⁻¹ * x) ∂μ) = 0
    simp
  mul_zero f := by
    ext x
    change (∫ y, f y * (0 : ℂ) ∂μ) = 0
    simp

instance : IsScalarTower ℂ (HeckeAlgebra μ) (HeckeAlgebra μ) where
  smul_assoc := TestFunction.convolution_smul_left μ

instance : SMulCommClass ℂ (HeckeAlgebra μ) (HeckeAlgebra μ) where
  smul_comm c f g := (TestFunction.convolution_smul_right μ c f g).symm

end HeckeAlgebra

end Langlands.Hecke
