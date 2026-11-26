import Langlands.Geometry.Manifold.LieGroupIntegrationByParts
import Langlands.Automorphic.GroupSchemeEnvelopingAction
import Langlands.Global.InfiniteAdelicModularCharacter
import Langlands.Automorphic.GroupSchemeAdelicUniformGrowth

/-! # Transposes of enveloping operators on the infinite adelic points

For a group scheme `G` with a smooth structure, the actual enveloping action on plot-smooth
functions on `G(F_∞)` has transposes on compactly supported plot-smooth functions with respect to
every right-invariant measure: for each element `y` of the complex enveloping algebra there is an
operator `T` with `∫ (y f) ψ dν = ∫ f (T ψ) dν`. Compactly supported plot-smooth functions
separate continuous functions for measures positive on open sets. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.Automorphic.GroupSchemeFunctions Langlands.Geometry.Manifold

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  {d : ℕ}

/-- Plot-smooth functions on `G(F_∞)` with compact support. -/
def compactPlotSmoothFunctions : Submodule ℂ (InfinitePlotSmoothFunctions F G) where
  carrier := {ψ | HasCompactSupport (ψ : InfiniteAdelicGroupPoints F G → ℂ)}
  zero_mem' := HasCompactSupport.zero
  add_mem' hψ hφ := hψ.add hφ
  smul_mem' c _ hψ := hψ.smul_left (f := fun _ => c)

variable {F G}

theorem continuous_of_mem_infinitePlotSmoothFunctions
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) {f : InfiniteAdelicGroupPoints F G → ℂ}
    (hf : f ∈ InfinitePlotSmoothFunctions F G) : Continuous f := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  exact ((isPlotSmooth_iff_contMDiff F G hsmooth f).mp hf).continuous

theorem integrable_mul_compactPlotSmooth (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (ν : Measure (InfiniteAdelicGroupPoints F G)) [IsFiniteMeasureOnCompacts ν]
    (f : InfinitePlotSmoothFunctions F G) (ψ : compactPlotSmoothFunctions F G) :
    Integrable (fun x => (f : InfiniteAdelicGroupPoints F G → ℂ) x *
      ((ψ : InfinitePlotSmoothFunctions F G) : InfiniteAdelicGroupPoints F G → ℂ) x) ν :=
  ((continuous_of_mem_infinitePlotSmoothFunctions hsmooth f.property).mul
    (continuous_of_mem_infinitePlotSmoothFunctions hsmooth ψ.val.property)).integrable_of_hasCompactSupport
    (HasCompactSupport.mul_left ψ.property)

variable (F G)

/-- Every element of the complex enveloping algebra has a transpose on compactly supported
plot-smooth functions for a right-invariant measure. -/
theorem exists_envelopingAction_transpose (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (ν : Measure (InfiniteAdelicGroupPoints F G)) [ν.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts ν] (y : AdelicEnvelopingAlgebra F G hsmooth) :
    ∃ T : compactPlotSmoothFunctions F G → compactPlotSmoothFunctions F G,
      ∀ (f : InfinitePlotSmoothFunctions F G) (ψ : compactPlotSmoothFunctions F G),
        ∫ x, ((plotSmoothEnvelopingAction F G hsmooth hcalc y f :
            InfinitePlotSmoothFunctions F G) : InfiniteAdelicGroupPoints F G → ℂ) x *
            ((ψ : InfinitePlotSmoothFunctions F G) : InfiniteAdelicGroupPoints F G → ℂ) x ∂ν =
          ∫ x, (f : InfiniteAdelicGroupPoints F G → ℂ) x *
            (((T ψ : compactPlotSmoothFunctions F G) : InfinitePlotSmoothFunctions F G) :
              InfiniteAdelicGroupPoints F G → ℂ) x ∂ν := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  let ρ := plotSmoothEnvelopingAction F G hsmooth hcalc
  -- the transposable elements
  let P : AdelicEnvelopingAlgebra F G hsmooth → Prop := fun y =>
    ∃ T : compactPlotSmoothFunctions F G → compactPlotSmoothFunctions F G,
      ∀ (f : InfinitePlotSmoothFunctions F G) (ψ : compactPlotSmoothFunctions F G),
        ∫ x, ((ρ y f : InfinitePlotSmoothFunctions F G) : InfiniteAdelicGroupPoints F G → ℂ) x *
            ((ψ : InfinitePlotSmoothFunctions F G) : InfiniteAdelicGroupPoints F G → ℂ) x ∂ν =
          ∫ x, (f : InfiniteAdelicGroupPoints F G → ℂ) x *
            (((T ψ : compactPlotSmoothFunctions F G) : InfinitePlotSmoothFunctions F G) :
              InfiniteAdelicGroupPoints F G → ℂ) x ∂ν
  have hadd : ∀ a b, P a → P b → P (a + b) := by
    rintro a b ⟨Ta, hTa⟩ ⟨Tb, hTb⟩
    refine ⟨fun ψ => Ta ψ + Tb ψ, fun f ψ => ?_⟩
    simp only [map_add, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, add_mul, mul_add]
    rw [integral_add (integrable_mul_compactPlotSmooth hsmooth ν _ ψ)
        (integrable_mul_compactPlotSmooth hsmooth ν _ ψ),
      integral_add (integrable_mul_compactPlotSmooth hsmooth ν f _)
        (integrable_mul_compactPlotSmooth hsmooth ν f _), hTa, hTb]
  have hmul : ∀ a b, P a → P b → P (a * b) := by
    rintro a b ⟨Ta, hTa⟩ ⟨Tb, hTb⟩
    refine ⟨fun ψ => Tb (Ta ψ), fun f ψ => ?_⟩
    rw [map_mul, Module.End.mul_apply, hTa, hTb]
  have hsmul : ∀ (c : ℂ) a, P a → P (c • a) := by
    rintro c a ⟨Ta, hTa⟩
    refine ⟨fun ψ => c • Ta ψ, fun f ψ => ?_⟩
    simp only [map_smul, LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [show (fun x => c * ((ρ a f : InfinitePlotSmoothFunctions F G) :
          InfiniteAdelicGroupPoints F G → ℂ) x *
          ((ψ : InfinitePlotSmoothFunctions F G) : InfiniteAdelicGroupPoints F G → ℂ) x) =
        fun x => c * (((ρ a f : InfinitePlotSmoothFunctions F G) :
          InfiniteAdelicGroupPoints F G → ℂ) x *
          ((ψ : InfinitePlotSmoothFunctions F G) : InfiniteAdelicGroupPoints F G → ℂ) x) by
        funext x; ring,
      integral_const_mul, hTa, ← integral_const_mul]
    congr 1
    funext x
    ring
  have hone : P 1 := ⟨id, fun f ψ => by simp [ρ]⟩
  have hgen : ∀ (X : GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)), P (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) := by
    intro X
    let D : compactPlotSmoothFunctions F G → compactPlotSmoothFunctions F G := fun ψ =>
      ⟨-(plotSmoothDifferential F G hsmooth X ψ.val), by
        change HasCompactSupport (fun x => -(groupDirectionalValue 𝓘(ℝ, smoothModel F d) X
          ((ψ : InfinitePlotSmoothFunctions F G) : InfiniteAdelicGroupPoints F G → ℂ) x))
        exact (HasCompactSupport.groupDirectionalValue X ψ.property).neg⟩
    refine ⟨D, fun f ψ => ?_⟩
    have hgenρ : ρ (UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X)) =
        plotSmoothDifferential F G hsmooth X :=
      plotSmoothEnvelopingAction_real_generator F G hsmooth hcalc X
    rw [hgenρ]
    change ∫ x, groupDirectionalValue 𝓘(ℝ, smoothModel F d) X
        (f : InfiniteAdelicGroupPoints F G → ℂ) x *
        ((ψ : InfinitePlotSmoothFunctions F G) : InfiniteAdelicGroupPoints F G → ℂ) x ∂ν =
      ∫ x, (f : InfiniteAdelicGroupPoints F G → ℂ) x *
        -(groupDirectionalValue 𝓘(ℝ, smoothModel F d) X
          ((ψ : InfinitePlotSmoothFunctions F G) : InfiniteAdelicGroupPoints F G → ℂ) x) ∂ν
    rw [integral_groupDirectionalValue_mul ν X
      ((isPlotSmooth_iff_contMDiff F G hsmooth _).mp f.property)
      ((isPlotSmooth_iff_contMDiff F G hsmooth _).mp ψ.val.property) ψ.property]
    rw [← integral_neg]
    congr 1
    funext x
    ring
  have hι : ∀ Z : ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G),
      P (UniversalEnvelopingAlgebra.ι ℂ Z) := by
    intro Z
    induction Z using TensorProduct.inductionOn with
    | tmul c X =>
      have h : UniversalEnvelopingAlgebra.ι ℂ (c ⊗ₜ[ℝ] X) =
          c • UniversalEnvelopingAlgebra.ι ℂ ((1 : ℂ) ⊗ₜ[ℝ] X) := by
        rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h]
      exact hsmul c _ (hgen X)
    | add Z W hZ hW => simpa only [map_add] using hadd _ _ hZ hW
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ
      (ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))) y
  change P (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ t)
  induction t using TensorAlgebra.induction with
  | algebraMap c =>
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    exact hsmul c 1 hone
  | «ι» Z =>
    change P (UniversalEnvelopingAlgebra.ι ℂ Z)
    exact hι Z
  | mul a b ha hb => simpa only [map_mul] using hmul _ _ ha hb
  | add a b ha hb => simpa only [map_add] using hadd _ _ ha hb

/-- Compactly supported plot-smooth functions separate continuous functions on `G(F_∞)` for a
measure that is finite on compact sets and positive on nonempty open sets. -/
theorem eq_zero_of_forall_integral_compactPlotSmooth (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (ν : Measure (InfiniteAdelicGroupPoints F G)) [ν.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts ν] {Θ : InfiniteAdelicGroupPoints F G → ℂ} (hΘ : Continuous Θ)
    (h : ∀ ψ : compactPlotSmoothFunctions F G,
      ∫ x, Θ x * ((ψ : InfinitePlotSmoothFunctions F G) : InfiniteAdelicGroupPoints F G → ℂ) x ∂ν
        = 0) :
    Θ = 0 := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  refine eq_zero_of_forall_integral_mul_eq_zero (E := smoothModel F d) ν hΘ fun ψ hψ hψc => ?_
  exact h ⟨⟨ψ, (isPlotSmooth_iff_contMDiff F G hsmooth ψ).mpr hψ⟩, hψc⟩

end Langlands.Global.InfiniteAdelicGroupPoints
