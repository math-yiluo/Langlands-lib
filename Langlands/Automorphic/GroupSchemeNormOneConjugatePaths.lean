import Langlands.Automorphic.GroupSchemeNormOneDirectional
import Langlands.Global.InfiniteAdelicGroupManifold
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Conjugated coordinate paths in the archimedean norm-one group

Let `A` be an embedded Lie atlas on `G(F∞)¹` and `Ψ : E → G(F∞)` a smooth map with values in
`G(F∞)¹`. For `k ∈ G(F∞)` and `v ∈ E` the path `s ↦ k⁻¹ Ψ(s v) k` lies in `G(F∞)¹` and is smooth
for `A`. Its velocity, translated to the identity, has norm at most a constant times `‖v‖`,
uniformly for `k` in a compact set and `v` in a closed ball. -/

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NumberField Set Metric
open scoped CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.InfiniteAdelicGroupPoints
  Langlands.Geometry.Manifold

set_option backward.isDefEq.respectTransparency false

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {d e : ℕ} {hsmooth : SmoothOfRelativeDimension d G.X.hom}

local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "G∞¹" => infiniteNormOneSubgroup F G
local notation "IE" => 𝓘(ℝ, Fin e → ℝ)
local notation "IG" => 𝓘(ℝ, smoothModel F d)

/-- Infinite adelic points conjugate norm-one archimedean points to norm-one points. -/
theorem conj_mem_infiniteNormOneSubgroup (k : G∞) {h : G∞} (hh : h ∈ G∞¹) :
    k⁻¹ * h * k ∈ G∞¹ := by
  change ofInfinite F G (k⁻¹ * h * k) ∈ normOneSubgroup F G
  rw [map_mul, map_mul, map_inv]
  have hh' : ofInfinite F G h ∈ normOneSubgroup F G := hh
  have hn := (normOneSubgroup_normal F G).conj_mem _ hh' (ofInfinite F G k)⁻¹
  rw [inv_inv] at hn
  exact hn

/-- **Smoothness into the norm-one group.** A map into `G(F∞)¹` is smooth for an embedded atlas
when it is continuous and smooth as a map into `G(F∞)`. -/
theorem contMDiff_infiniteNormOne_of_val (A : NormOneLieAtlas F G hsmooth e)
    {Es : Type*} [NormedAddCommGroup Es] [NormedSpace ℝ Es] {HM : Type*} [TopologicalSpace HM]
    {IM : ModelWithCorners ℝ Es HM}
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M]
    {f : M → G∞¹} (hc : Continuous f) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := A.chartedSpace
    ContMDiff IM IG ∞ (fun x => (f x : G∞)) → ContMDiff IM IE ∞ f := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := A.chartedSpace
  let : IsManifold IG ∞ G∞ := smoothIsManifold F G hsmooth
  let := A.isManifold
  intro hs
  exact (ContMDiff.iff_comp_isImmersion A.immersion).mpr ⟨hc, hs⟩

section Conjugate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The point `k⁻¹ Ψ(z)⁻¹ Ψ(y) k` of `G(F∞)¹`. -/
def conjugateDisplacement (Ψ : E → G∞) (hΨ₁ : ∀ v, Ψ v ∈ G∞¹) (k : G∞) (z y : E) : G∞¹ :=
  ⟨k⁻¹ * ((Ψ z)⁻¹ * Ψ y) * k, by
    apply conj_mem_infiniteNormOneSubgroup
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hΨ₁ z)) (hΨ₁ y)⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] theorem conjugateDisplacement_val (Ψ : E → G∞) (hΨ₁ : ∀ v, Ψ v ∈ G∞¹) (k : G∞)
    (z y : E) :
    (conjugateDisplacement Ψ hΨ₁ k z y : G∞) = k⁻¹ * ((Ψ z)⁻¹ * Ψ y) * k := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem conjugateDisplacement_self (Ψ : E → G∞) (hΨ₁ : ∀ v, Ψ v ∈ G∞¹) (k : G∞) (z : E) :
    conjugateDisplacement Ψ hΨ₁ k z z = 1 := by
  apply Subtype.ext
  simp

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem conjugateDisplacement_inv_mul (Ψ : E → G∞) (hΨ₁ : ∀ v, Ψ v ∈ G∞¹) (k : G∞)
    (z y y' : E) :
    (conjugateDisplacement Ψ hΨ₁ k z y)⁻¹ * conjugateDisplacement Ψ hΨ₁ k z y' =
      conjugateDisplacement Ψ hΨ₁ k y y' := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjugateDisplacement_val]
  group

/-- The displacement is jointly smooth for the embedded atlas. -/
theorem contMDiff_conjugateDisplacement (A : NormOneLieAtlas F G hsmooth e) (Ψ : E → G∞)
    (hΨ₁ : ∀ v, Ψ v ∈ G∞¹) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := A.chartedSpace
    ContMDiff 𝓘(ℝ, E) IG ∞ Ψ →
    ContMDiff (ModelWithCorners.prod (ModelWithCorners.prod IG 𝓘(ℝ, E)) 𝓘(ℝ, E)) IE ∞
      (fun p : (G∞ × E) × E => conjugateDisplacement Ψ hΨ₁ p.1.1 p.1.2 p.2) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := A.chartedSpace
  let : IsManifold IG ∞ G∞ := smoothIsManifold F G hsmooth
  let := smoothLieGroup F G hsmooth
  intro hΨ
  have hval : ContMDiff (ModelWithCorners.prod (ModelWithCorners.prod IG 𝓘(ℝ, E)) 𝓘(ℝ, E)) IG ∞
      (fun p : (G∞ × E) × E => p.1.1⁻¹ * ((Ψ p.1.2)⁻¹ * Ψ p.2) * p.1.1) :=
    ((contMDiff_fst.comp contMDiff_fst).inv.mul
      ((hΨ.comp (contMDiff_snd.comp contMDiff_fst)).inv.mul (hΨ.comp contMDiff_snd))).mul
      (contMDiff_fst.comp contMDiff_fst)
  refine contMDiff_infiniteNormOne_of_val A ?_ hval
  exact Continuous.subtype_mk hval.continuous _

/-- The differential at `z` of `y ↦ k⁻¹ Ψ(z)⁻¹ Ψ(y) k`, a linear map into the tangent space
`Fin e → ℝ` at the identity of `G(F∞)¹`. -/
def conjugateDifferential (A : NormOneLieAtlas F G hsmooth e) (Ψ : E → G∞)
    (hΨ₁ : ∀ v, Ψ v ∈ G∞¹) (p : G∞ × E) : E →L[ℝ] (Fin e → ℝ) :=
  letI := A.chartedSpace
  mfderiv 𝓘(ℝ, E) IE (conjugateDisplacement Ψ hΨ₁ p.1 p.2) p.2

/-- The differential of the displacement depends continuously on `(k, z)`. -/
theorem continuous_conjugateDifferential (A : NormOneLieAtlas F G hsmooth e)
    (Ψ : E → G∞) (hΨ₁ : ∀ v, Ψ v ∈ G∞¹) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    ContMDiff 𝓘(ℝ, E) IG ∞ Ψ → Continuous (conjugateDifferential A Ψ hΨ₁) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := A.chartedSpace
  let : IsManifold IG ∞ G∞ := smoothIsManifold F G hsmooth
  let := A.isManifold
  let := A.lieGroup
  intro hΨ
  let H (p : G∞ × E) (y : E) := conjugateDisplacement Ψ hΨ₁ p.1 p.2 y
  have hH : ContMDiff (ModelWithCorners.prod (ModelWithCorners.prod IG 𝓘(ℝ, E)) 𝓘(ℝ, E)) IE ∞
      (Function.uncurry H) := contMDiff_conjugateDisplacement A Ψ hΨ₁ hΨ
  have hH₁ (p : G∞ × E) : H p p.2 = 1 := conjugateDisplacement_self Ψ hΨ₁ p.1 p.2
  apply continuous_iff_continuousAt.mpr
  intro p
  have hp := (hH (p, p.2)).mfderiv H Prod.snd
    (contMDiffAt_snd : ContMDiffAt (ModelWithCorners.prod IG 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ Prod.snd p)
    (m := ∞) (by simp)
  have heq :
      inTangentCoordinates 𝓘(ℝ, E) IE Prod.snd (fun z => H z z.2)
        (fun z => mfderiv 𝓘(ℝ, E) IE (H z) z.2) p =
          (fun q : G∞ × E => show E →L[ℝ] (Fin e → ℝ) from mfderiv 𝓘(ℝ, E) IE (H q) q.2) := by
    funext q
    rw [inTangentCoordinates_eq _ _ _ (by simp) (by simp [hH₁])]
    simp only [tangentBundleCore_coordChange_model_space, hH₁, ContinuousLinearMap.comp_id]
    let Lq : E →L[ℝ] (Fin e → ℝ) := mfderiv 𝓘(ℝ, E) IE (H q) q.2
    change ((tangentBundleCore IE G∞¹).coordChange (achart (Fin e → ℝ) 1)
      (achart (Fin e → ℝ) 1) 1).comp Lq = Lq
    refine ContinuousLinearMap.ext fun y => ?_
    exact (tangentBundleCore IE G∞¹).coordChange_self (achart (Fin e → ℝ) 1) 1
      (mem_achart_source (Fin e → ℝ) 1) (Lq y)
  have hc : ContinuousAt (fun q : G∞ × E =>
      show E →L[ℝ] (Fin e → ℝ) from mfderiv 𝓘(ℝ, E) IE (H q) q.2) p := by
    simpa only [heq] using hp.continuousAt
  exact hc

/-- The coordinate path `s ↦ k⁻¹ Ψ(0)⁻¹ Ψ(s v) k` in `G(F∞)¹`. -/
def conjugatePath (Ψ : E → G∞) (hΨ₁ : ∀ v, Ψ v ∈ G∞¹) (k : G∞) (w : E) (s : ℝ) : G∞¹ :=
  conjugateDisplacement Ψ hΨ₁ k 0 (s • w)

theorem conjugatePath_zero (Ψ : E → G∞) (hΨ₁ : ∀ v, Ψ v ∈ G∞¹) (k : G∞) (w : E) :
    conjugatePath Ψ hΨ₁ k w 0 = 1 := by
  simp only [conjugatePath, zero_smul]
  exact conjugateDisplacement_self Ψ hΨ₁ k 0

theorem conjugatePath_val (Ψ : E → G∞) (hΨ₁ : ∀ v, Ψ v ∈ G∞¹) (hΨ₀ : Ψ 0 = 1) (k : G∞) (w : E)
    (s : ℝ) : (conjugatePath Ψ hΨ₁ k w s : G∞) = k⁻¹ * Ψ (s • w) * k := by
  simp [conjugatePath, hΨ₀]

set_option maxHeartbeats 1000000 in
/-- The coordinate path is smooth for the embedded atlas. -/
theorem contMDiff_conjugatePath (A : NormOneLieAtlas F G hsmooth e) (Ψ : E → G∞)
    (hΨ₁ : ∀ v, Ψ v ∈ G∞¹) (k : G∞) (w : E) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := A.chartedSpace
    ContMDiff 𝓘(ℝ, E) IG ∞ Ψ → ContMDiff 𝓘(ℝ, ℝ) IE ∞ (conjugatePath Ψ hΨ₁ k w) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := A.chartedSpace
  let : IsManifold IG ∞ G∞ := smoothIsManifold F G hsmooth
  intro hΨ
  have hlin : ContMDiff 𝓘(ℝ, ℝ) (ModelWithCorners.prod (ModelWithCorners.prod IG 𝓘(ℝ, E)) 𝓘(ℝ, E)) ∞
      (fun s : ℝ => ((k, (0 : E)), s • w)) := by
    apply ContMDiff.prodMk contMDiff_const
    exact (contDiff_id.smul contDiff_const).contMDiff
  have h2 := (contMDiff_conjugateDisplacement A Ψ hΨ₁ hΨ).comp hlin
  exact h2

set_option maxHeartbeats 1000000 in
/-- The translated velocity of the coordinate path is the differential of the displacement
applied to `v`. -/
theorem leftPathVelocity_conjugatePath (A : NormOneLieAtlas F G hsmooth e) (Ψ : E → G∞)
    (hΨ₁ : ∀ v, Ψ v ∈ G∞¹) (k : G∞) (w : E) (s : ℝ) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := A.chartedSpace
    letI := A.lieGroup
    ContMDiff 𝓘(ℝ, E) IG ∞ Ψ →
    leftPathVelocity (conjugatePath Ψ hΨ₁ k w) s = conjugateDifferential A Ψ hΨ₁ (k, s • w) w := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := A.chartedSpace
  let := A.lieGroup
  let : IsManifold IG ∞ G∞ := smoothIsManifold F G hsmooth
  intro hΨ
  have hpair : ContMDiff 𝓘(ℝ, E) (ModelWithCorners.prod (ModelWithCorners.prod IG 𝓘(ℝ, E))
      𝓘(ℝ, E)) ∞ (fun y : E => ((k, s • w), y)) := by
    apply ContMDiff.prodMk contMDiff_const
    exact contMDiff_id
  have hg : ContMDiff 𝓘(ℝ, E) IE ∞ (conjugateDisplacement Ψ hΨ₁ k (s • w)) := by
    have h2 := (contMDiff_conjugateDisplacement A Ψ hΨ₁ hΨ).comp hpair
    exact h2
  have hgd := (hg.mdifferentiableAt (x := s • w) (by simp)).hasMFDerivAt
  have hfd : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s' : ℝ => s' • w) s
      ((ContinuousLinearMap.id ℝ ℝ).smulRight w) :=
    ((hasFDerivAt_id s).smul_const w).hasMFDerivAt
  have hcomp := hgd.comp s hfd
  have hcongr := hcomp.congr_of_eventuallyEq
    (f₁ := fun s' : ℝ => (conjugatePath Ψ hΨ₁ k w s)⁻¹ * conjugatePath Ψ hΨ₁ k w s')
    (Filter.Eventually.of_forall fun s' =>
      conjugateDisplacement_inv_mul Ψ hΨ₁ k 0 (s • w) (s' • w))
  unfold leftPathVelocity
  rw [hcongr.mfderiv]
  change (mfderiv 𝓘(ℝ, E) IE (conjugateDisplacement Ψ hΨ₁ k (s • w)) (s • w))
    (((ContinuousLinearMap.id ℝ ℝ).smulRight w) (1 : ℝ)) = _
  rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, one_smul]
  rfl

/-- **Velocity bound.** For `k` in a compact set and `v` in a closed ball, the translated velocity
of the coordinate path at times `s ∈ [0, 1]` (`leftPathVelocity_conjugatePath`) has norm at most a
constant times `‖v‖`. -/
theorem exists_norm_conjugateDifferential_le [FiniteDimensional ℝ E]
    (A : NormOneLieAtlas F G hsmooth e)
    (Ψ : E → G∞) (hΨ₁ : ∀ v, Ψ v ∈ G∞¹) (K : Set G∞) (hK : IsCompact K) (B : ℝ) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    letI := A.chartedSpace
    letI := A.lieGroup
    ContMDiff 𝓘(ℝ, E) IG ∞ Ψ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ∈ K, ∀ w ∈ closedBall (0 : E) B, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖conjugateDifferential A Ψ hΨ₁ (k, s • w) w‖ ≤ C * ‖w‖ := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := A.chartedSpace
  let := A.lieGroup
  intro hΨ
  have hL := continuous_conjugateDifferential A Ψ hΨ₁ hΨ
  obtain ⟨D, hD⟩ := ((hK.prod (isCompact_closedBall (0 : E) B)).image hL.norm).bddAbove
  refine ⟨max 0 D, le_max_left _ _, fun k hk w hv s hs => ?_⟩
  have hsv : s • w ∈ closedBall (0 : E) B := by
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hs.1]
    rw [mem_closedBall, dist_zero_right] at hv
    exact (mul_le_of_le_one_left (norm_nonneg w) hs.2).trans hv
  have hLB : ‖conjugateDifferential A Ψ hΨ₁ (k, s • w)‖ ≤ max 0 D :=
    (hD ⟨(k, s • w), ⟨hk, hsv⟩, rfl⟩).trans (le_max_right _ _)
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right hLB (norm_nonneg w))

end Conjugate

end Langlands.Automorphic.GroupSchemeFunctions
