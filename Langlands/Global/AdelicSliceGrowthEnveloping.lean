import Langlands.Global.AdelicSliceGrowthFamily
import Langlands.Automorphic.GroupSchemeAutomorphicFunctionUniformGrowthStatement
import Langlands.Automorphic.GroupSchemeManifoldSmooth

/-! # Uniform slice growth from uniformly moderate growth

The enveloping element `ι(1 ⊗ Xₖ) ⋯ ι(1 ⊗ X₁)` acts on plot-smooth infinite slices as the
iterated invariant derivative along `[X₁, …, Xₖ]`. So an automorphic function with uniformly
moderate growth (`HasUniformModerateGrowthFunction`) for a closed representation of positive size
has uniform slice growth for the adelic height, with one nonnegative exponent. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open InfiniteAdelicGroupPoints Langlands.Geometry.Manifold Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

local notation "𝓘∞" => 𝓘(ℝ, smoothModel F d)
local notation "𝓘ℂ" => 𝓘(ℝ, ℂ)
local notation "Adeles" => AdelicGroupPoints F G

/-- The enveloping element `ι(1 ⊗ Xₖ) ⋯ ι(1 ⊗ X₁)` of the list `[X₁, …, Xₖ]`. -/
def envelopingWord (w : List (smoothModel F d)) : AdelicEnvelopingAlgebra F G hsmooth := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hsmooth
  letI := smoothLieGroup F G hsmooth
  letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  exact w.foldr (fun X a => a * UniversalEnvelopingAlgebra.ι ℂ
    (L := ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
    ((1 : ℂ) ⊗ₜ[ℝ] X)) 1

theorem envelopingWord_nil :
    envelopingWord hsmooth ([] : List (smoothModel F d)) = 1 := rfl

theorem envelopingWord_cons (X : smoothModel F d) (w : List (smoothModel F d)) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := smoothLieGroup F G hsmooth
    letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
    envelopingWord hsmooth (X :: w) = envelopingWord hsmooth w * UniversalEnvelopingAlgebra.ι ℂ
      (L := ℂ ⊗[ℝ] GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G))
      ((1 : ℂ) ⊗ₜ[ℝ] X) := rfl

/-- The enveloping word acts on plot-smooth functions as the iterated invariant derivative. -/
theorem plotSmoothEnvelopingAction_envelopingWord
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (w : List (smoothModel F d)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    ∀ (f : InfiniteAdelicGroupPoints F G → ℂ) (hf : f ∈ InfinitePlotSmoothFunctions F G),
      ((plotSmoothEnvelopingAction F G hsmooth hcalc (envelopingWord hsmooth w) ⟨f, hf⟩ :
          InfinitePlotSmoothFunctions F G) : InfiniteAdelicGroupPoints F G → ℂ) =
        listDirectionalDerivative (G := InfiniteAdelicGroupPoints F G) w f := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  induction w with
  | nil =>
    intro f hf
    rw [envelopingWord_nil, map_one, Module.End.one_apply]
    rfl
  | cons X w ih =>
    intro f hf
    rw [envelopingWord_cons, map_mul, Module.End.mul_apply,
      plotSmoothEnvelopingAction_real_generator F G hsmooth hcalc X]
    exact ih (plotSmoothDifferential F G hsmooth X ⟨f, hf⟩).val
      (plotSmoothDifferential F G hsmooth X ⟨f, hf⟩).property

/-- An automorphic function with uniformly moderate growth for a closed representation of
positive size has uniform slice growth for the adelic height with a nonnegative exponent. -/
theorem exists_hasUniformSliceGrowth {N : ℕ}
    (rho : GroupScheme.MatrixRepresentation G (Fin N)) (hN : 0 < N)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) (Γ : Subgroup Adeles)
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) {φ : Adeles → ℂ}
    (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc Γ Kinf rho φ)
    (hg : HasUniformModerateGrowthFunction F G rho hsmooth hcalc φ) :
    ∃ e : ℝ, 0 ≤ e ∧
      HasUniformSliceGrowth hsmooth Γ (RepresentationGrowth.adelicHeight F G rho) e φ := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  obtain ⟨r, hr⟩ := hg
  have hslice : ∀ b, functionInfiniteSlice F G φ b ∈ InfinitePlotSmoothFunctions F G :=
    hφ.2.1.2.1
  let H := RepresentationGrowth.adelicHeight F G rho
  let scale : ℝ := (N : ℝ) ^ (∑ v : InfinitePlace F, v.mult)
  have hscale : 0 < scale := pow_pos (Nat.cast_pos.mpr hN) _
  have hH1 (g : Adeles) : 1 ≤ H g := RepresentationGrowth.one_le_adelicHeight F G rho hN g
  refine ⟨max r 0, le_max_right _ _, fun b =>
    (isPlotSmooth_iff_contMDiff F G hsmooth _).mp (hslice b), hφ.1, fun v => ?_⟩
  obtain ⟨C, hC, hb⟩ := hr (envelopingWord hsmooth v)
  refine ⟨C * scale⁻¹ ^ r, fun b a => ?_⟩
  have hact := plotSmoothEnvelopingAction_envelopingWord hsmooth hcalc v
    (functionInfiniteSlice F G φ b) (hslice b)
  have hbound := hb b (hslice b) a
  rw [hact] at hbound
  have hsrc : RepresentationGrowth.adelicSourceNorm F G rho (pair F G a b) =
      scale⁻¹ * H (pair F G a b) := by
    rw [show H (pair F G a b) = scale *
        RepresentationGrowth.adelicSourceNorm F G rho (pair F G a b) from
      RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm F G rho _]
    rw [← mul_assoc, inv_mul_cancel₀ hscale.ne', one_mul]
  have hH0 : 0 ≤ H (pair F G a b) := zero_le_one.trans (hH1 _)
  rw [hsrc, Real.mul_rpow (inv_nonneg.mpr hscale.le) hH0] at hbound
  calc _ ≤ C * (scale⁻¹ ^ r * H (pair F G a b) ^ r) := hbound
    _ ≤ C * (scale⁻¹ ^ r * H (pair F G a b) ^ max r 0) := by
        gcongr
        · exact hH1 _
        · exact le_max_left _ _
    _ = C * scale⁻¹ ^ r * H (pair F G a b) ^ max r 0 := by ring

end Langlands.Global.AdelicGroupPoints
