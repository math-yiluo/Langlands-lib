import Langlands.Global.InfiniteAdelicGroupManifold
import Langlands.Global.InfinitePlaceRealizationSmooth
import Langlands.Geometry.Manifold.ZeroDirectionalDerivative
import Langlands.GroupScheme.AffinePointFiniteCoordinates

/-! # The chart of the infinite adelic point group at a point, in regular coordinates

The published atlas on `G(F ⊗ ℝ)` is the pullback, through the completion decomposition, of the
product of the place-wise atlases, each the pullback through algebraic base change of a chosen
regular atlas. This module records the resulting formula for the extended chart.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.GroupScheme Langlands.GroupScheme.General
open Langlands.AlgebraicGeometry.PointManifold.General

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] {d : ℕ}

/-- The regular chart of `G(F_v)` at a point, from the chosen regular atlas of the base
change. -/
abbrev placeRegularChart (hsmooth : SmoothOfRelativeDimension d G.X.hom) (v : InfinitePlace F)
    (x : InfinitePlaceGroupPoints F G v) :=
  letI := InfinitePlaceGroupPoints.completionRCLike F v
  (smoothAffineRegularAtlas (affineBaseChange_smooth F v.Completion G hsmooth)).chartAt
    (affineBaseChangePointHomeomorph F v.Completion G x)

theorem extChartAt_apply (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (x g : InfiniteAdelicGroupPoints F G) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    extChartAt 𝓘(ℝ, smoothModel F d) x g =
      fun v => (placeRegularChart F G hsmooth v (atPlace F G v x)).homeomorph
        (letI := InfinitePlaceGroupPoints.completionRCLike F v
         affineBaseChangePointHomeomorph F v.Completion G (atPlace F G v g)) := by
  rfl

theorem mem_extChartAt_source_iff (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (x g : InfiniteAdelicGroupPoints F G) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    g ∈ (extChartAt 𝓘(ℝ, smoothModel F d) x).source ↔
      ∀ v, (letI := InfinitePlaceGroupPoints.completionRCLike F v
        affineBaseChangePointHomeomorph F v.Completion G (atPlace F G v g)) ∈
          (placeRegularChart F G hsmooth v (atPlace F G v x)).homeomorph.source := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  rw [extChartAt_source]
  exact Set.mem_univ_pi

omit [NumberField F] in
open Langlands.AlgebraicGeometry.PointTopology in
theorem regularEvaluation_affineBaseChangePointHomeomorph (v : InfinitePlace F)
    (y : InfinitePlaceGroupPoints F G v)
    (b : Γ((InfinitePlaceGroupPoints.completionBaseChange F G v).X.left, ⊤)) :
    letI := InfinitePlaceGroupPoints.completionRCLike F v
    regularEvaluation (affineBaseChangePointHomeomorph F v.Completion G y) b =
      (InfinitePlaceGroupPoints.completionBaseChange F G v).affinePointEvaluation
        (CommAlgCat.of v.Completion v.Completion)
        (affinePointsBaseChangeMulEquiv F v.Completion v.Completion G y) b := by
  let := InfinitePlaceGroupPoints.completionRCLike F v
  exact affinePointsRingPointHomeomorph_evaluation
    (InfinitePlaceGroupPoints.completionBaseChange F G v)
    (CommAlgCat.of v.Completion v.Completion)
    (affinePointsBaseChangeMulEquiv F v.Completion v.Completion G y) b

open Langlands.Geometry.Manifold.ZeroDirectionalDerivative in
/-- **Injectivity of the realization differentials.** A tangent vector at the identity along
which every matrix entry of every place-wise closed realization has zero derivative is zero. -/
theorem eq_zero_of_zeroDeriv_realization (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    {N : InfinitePlace F → ℕ}
    (ρ : ∀ v, MatrixRepresentation (InfinitePlaceGroupPoints.completionBaseChange F G v)
      (Fin (N v)))
    (hρ : ∀ v, IsClosedSubgroup (ρ v)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    ∀ X : TangentSpace 𝓘(ℝ, smoothModel F d) (1 : InfiniteAdelicGroupPoints F G),
      (∀ v i j, ZeroDeriv X (fun g =>
        (InfinitePlaceGroupPoints.realizationMatrix F G v (ρ v) (atPlace F G v g)).val i j)) →
      X = 0 := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.smoothChartedSpace F G v hsmooth
  let := smoothChartedSpace F G hsmooth
  have : IsManifold 𝓘(ℝ, smoothModel F d) ∞ (InfiniteAdelicGroupPoints F G) :=
    smoothIsManifold F G hsmooth
  have : LieGroup 𝓘(ℝ, smoothModel F d) ∞ (InfiniteAdelicGroupPoints F G) :=
    smoothLieGroup F G hsmooth
  intro X hX
  let R := fun v => InfinitePlaceGroupPoints.realizationMatrix F G v (ρ v)
  have hplace (v : InfinitePlace F) :
      ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, Fin d → v.Completion) ∞ (atPlace F G v) :=
    (contMDiff_iff_places F G 𝓘(ℝ, smoothModel F d) hsmooth id).mp contMDiff_id v
  have hentry (v : InfinitePlace F) (i j : Fin (N v)) :
      ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) ∞
        (fun g => (R v (atPlace F G v g)).val i j) :=
    (InfinitePlaceGroupPoints.contMDiff_iff_realizationMatrix F G v 𝓘(ℝ, smoothModel F d)
      hsmooth (ρ v) (hρ v) (atPlace F G v)).mp (hplace v) i j
  have hinvsmooth (v : InfinitePlace F) (i j : Fin (N v)) :
      ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) ∞
        (fun g => ((R v (atPlace F G v g))⁻¹).val i j) := by
    have h := (hentry v i j).comp (contMDiff_inv 𝓘(ℝ, smoothModel F d) ∞)
    convert h using 2 with g
    simp only [Function.comp_apply, map_inv]
  have hinv (v : InfinitePlace F) (i j : Fin (N v)) :
      ZeroDeriv X (fun g => ((R v (atPlace F G v g))⁻¹).val i j) :=
    zeroDeriv_of_mul_eq_one (A := fun g => (R v (atPlace F G v g)).val)
      (B := fun g => ((R v (atPlace F G v g))⁻¹).val)
      (fun g => (R v (atPlace F G v g)).mul_inv) (by simp [R]) (hX v)
      (fun i j => (hinvsmooth v i j).mdifferentiableAt (by simp)) i j
  have hreg (v : InfinitePlace F)
      (b : Γ((InfinitePlaceGroupPoints.completionBaseChange F G v).X.left, ⊤)) :
      ZeroDeriv X (fun g => Langlands.AlgebraicGeometry.PointManifold.General.regularEvaluation
        (affineBaseChangePointHomeomorph F v.Completion G (atPlace F G v g)) b) := by
    obtain ⟨P, hP⟩ := MatrixRepresentation.exists_polynomial_affinePointEvaluation (ρ v) (hρ v) b
    have h := zeroDeriv_aeval (X := X)
      (f := fun s g => GeneralLinear.values (R v (atPlace F G v g)) s) (fun s => by
        cases s with
        | entry i j => exact hX v i j
        | inverseEntry i j => exact hinv v i j) P
    refine h.congr (Filter.Eventually.of_forall fun g => ?_)
    dsimp only
    rw [regularEvaluation_affineBaseChangePointHomeomorph, hP]
    rfl
  have hcomp (v : InfinitePlace F) (k : Fin d) :
      ZeroDeriv X (fun g => extChartAt 𝓘(ℝ, smoothModel F d) (1 : InfiniteAdelicGroupPoints F G)
        g v k) := by
    let c := placeRegularChart F G hsmooth v (atPlace F G v 1)
    have hmem1 : affineBaseChangePointHomeomorph F v.Completion G (atPlace F G v 1) ∈
        c.homeomorph.source :=
      (smoothAffineRegularAtlas (affineBaseChange_smooth F v.Completion G hsmooth)).mem_source _
    let L : smoothModel F d →L[ℝ] v.Completion :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => v.Completion) k).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun w : InfinitePlace F => Fin d → w.Completion) v)
    have hsmoothc : MDifferentiableAt 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion)
        (fun g => extChartAt 𝓘(ℝ, smoothModel F d) (1 : InfiniteAdelicGroupPoints F G) g v k) 1 :=
      ((L.contDiff (n := ∞)).contMDiff.contMDiffAt.comp _
        (contMDiffAt_extChartAt (n := ∞))).mdifferentiableAt (by simp)
    have heq : (fun g => extChartAt 𝓘(ℝ, smoothModel F d) (1 : InfiniteAdelicGroupPoints F G)
          g v k) =ᶠ[nhds 1] fun g =>
        Langlands.AlgebraicGeometry.PointManifold.General.regularEvaluation
            (affineBaseChangePointHomeomorph F v.Completion G (atPlace F G v g)) (c.numerator k) /
          Langlands.AlgebraicGeometry.PointManifold.General.regularEvaluation
            (affineBaseChangePointHomeomorph F v.Completion G (atPlace F G v g))
              (c.denominator k) := by
      filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℝ, smoothModel F d))
        (1 : InfiniteAdelicGroupPoints F G)] with g hg
      rw [extChartAt_apply]
      exact c.apply_eq _ ((mem_extChartAt_source_iff F G hsmooth 1 g).mp hg v) k
    have hq := (hreg v (c.numerator k)).div (hreg v (c.denominator k))
      (c.denominator_ne_zero _ hmem1 k) (hsmoothc.congr_of_eventuallyEq heq.symm)
    exact hq.congr heq.symm
  have hchart : HasMFDerivAt 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, smoothModel F d)
      (extChartAt 𝓘(ℝ, smoothModel F d) (1 : InfiniteAdelicGroupPoints F G)) 1
      (ContinuousLinearMap.id ℝ (smoothModel F d)) := by
    have h := ((contMDiffAt_extChartAt (I := 𝓘(ℝ, smoothModel F d)) (n := ∞)
      (x := (1 : InfiniteAdelicGroupPoints F G))).mdifferentiableAt (by simp)).hasMFDerivAt
    rw [mfderiv_extChartAt_self] at h
    exact h
  have hvk (v : InfinitePlace F) (k : Fin d) : (X : smoothModel F d) v k = 0 := by
    let L : smoothModel F d →L[ℝ] v.Completion :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => v.Completion) k).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun w : InfinitePlace F => Fin d → w.Completion) v)
    obtain ⟨h', hh', hX'⟩ := hcomp v k
    have hL := (L.hasMFDerivAt (x := extChartAt 𝓘(ℝ, smoothModel F d)
      (1 : InfiniteAdelicGroupPoints F G) 1)).comp (1 : InfiniteAdelicGroupPoints F G) hchart
    have huniq := hL.mfderiv.symm.trans hh'.mfderiv
    have h1 := congrArg (fun T => T X) huniq
    change L X = h' X at h1
    rw [hX'] at h1
    exact h1
  funext v k
  exact hvk v k

end Langlands.Global.InfiniteAdelicGroupPoints
