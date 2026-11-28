import Langlands.Global.InfiniteAdelicTangentKernelNaturality
import Langlands.GroupScheme.ClosedImmersionPointLift

/-! # Velocities of curves in a closed subgroup at infinity -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable (F : Type u) [Field F] [NumberField F] {G V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine V.X.left] {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

/-- The dual-number point of the velocity at `0` of a smooth curve through the identity that
stays in the image of a closed subgroup `j : V ⟶ G` comes from a dual-number point of `V`. -/
theorem exists_tangentPoint_curve_eq_comp (j : V ⟶ G) [IsClosedImmersion j.hom.hom.left]
    (c : ℝ → InfiniteAdelicGroupPoints F G)
    (hc : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, smoothModel F d) ∞ c)
    (hc0 : c 0 = 1)
    (hcV : ∀ s, c s ∈ Set.range (V.affinePointsTarget j (CommAlgCat.of F (InfiniteAdeleRing F)))) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    ∃ y : Lie.AffinePoints V (DualNumber (InfiniteAdeleRing F)),
      y ≫ j.hom.hom = tangentPoint F hsmooth (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, smoothModel F d) c 0 1) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  have : IsManifold 𝓘(ℝ, smoothModel F d) ∞ (InfiniteAdelicGroupPoints F G) :=
    smoothIsManifold F G hsmooth
  let X : GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G) :=
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, smoothModel F d) c 0 1
  have hvanish (a : Γ(G.X.left, ⊤)) (ha : j.hom.hom.left.appTop a = 0) (s : ℝ) :
      G.affinePointEvaluation (CommAlgCat.of F (InfiniteAdeleRing F)) (c s) a = 0 := by
    obtain ⟨y, hy⟩ := hcV s
    rw [← hy, affinePointsTarget_apply, affinePointEvaluation_postcomp, ha, map_zero]
  refine exists_comp_eq_of_evaluation_eq_zero j (DualNumber (InfiniteAdeleRing F))
    (tangentPoint F hsmooth X) fun a ha => ?_
  have hev := affinePointEvaluation_tangentPoint F hsmooth X a
  refine hev.trans ?_
  apply TrivSqZeroExt.ext
  · refine (tangentAlgHom_fst F hsmooth X a).trans ?_
    have h := hvanish a ha 0
    rw [hc0] at h
    exact h
  · refine (tangentAlgHom_snd F hsmooth X a).trans ?_
    funext v
    have hconst : (placeValue F v a ∘ c) = fun _ => (0 : v.Completion) := by
      funext s
      change G.affinePointEvaluation (CommAlgCat.of F (InfiniteAdeleRing F)) (c s) a v = 0
      rw [hvanish a ha s]
      rfl
    have hchain := mfderiv_comp_apply_of_eq
      ((contMDiff_placeValue F hsmooth v a).mdifferentiable (by simp) (c 0))
      (hc.mdifferentiable (by simp) 0) rfl (1 : ℝ)
    rw [hconst, mfderiv_const] at hchain
    change (mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) (placeValue F v a) 1 X :
      v.Completion) = 0
    have h1 : c 0 = (1 : InfiniteAdelicGroupPoints F G) := hc0
    rw [h1] at hchain
    exact hchain.symm

/-- The Lie vector of the velocity at `0` of a smooth curve through the identity that stays in the
image of a closed subgroup `j : V ⟶ G` lies in the image of the Lie algebra of `V`. -/
theorem tangentKernel_curve_mem_range [IsAffineHom G.X.hom] [IsAffineHom V.X.hom]
    (j : V ⟶ G) [IsClosedImmersion j.hom.hom.left]
    (c : ℝ → InfiniteAdelicGroupPoints F G)
    (hc : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, smoothModel F d) ∞ c)
    (hc0 : c 0 = 1)
    (hcV : ∀ s, c s ∈ Set.range (V.affinePointsTarget j (CommAlgCat.of F (InfiniteAdeleRing F)))) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    Additive.ofMul (tangentKernel F hsmooth (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, smoothModel F d) c 0 1)) ∈
      LinearMap.range (Lie.targetMapLinear j (InfiniteAdeleRing F)) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  obtain ⟨y, hy⟩ := exists_tangentPoint_curve_eq_comp F hsmooth j c hc hc0 hcV
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have hmem : y ∈ (Lie.reduction V (A := InfiniteAdeleRing F)).ker :=
    mem_lieKernel_of_comp j y (by rw [hy]; exact reduction_tangentPoint F hsmooth _)
  refine ⟨Additive.ofMul ⟨y, hmem⟩, ?_⟩
  apply Additive.toMul.injective
  apply Subtype.ext
  exact hy

end Langlands.Global.InfiniteAdelicGroupPoints
