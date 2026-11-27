import Langlands.Global.InfiniteAdelicTangentKernel
import Langlands.Global.AdelicArchimedeanCharacterLog
import Langlands.Global.AdelicComplexParameters
import Langlands.Global.AdelicSquareIntegrableInducedForms
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Derivatives at the identity of archimedean logarithms of regular functions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField Filter Topology
open scoped CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

/-- In an `RCLike` field, `z ↦ log ‖z‖²` has derivative `2 Re` at `1`. -/
theorem hasFDerivAt_log_norm_sq_one (K : Type*) [RCLike K] :
    HasFDerivAt (fun z : K => Real.log (‖z‖ ^ 2)) (2 • (RCLike.reCLM : StrongDual ℝ K)) 1 := by
  have hn : (fun z : K => ‖z‖ ^ 2) =
      fun z => RCLike.re z * RCLike.re z + RCLike.im z * RCLike.im z := by
    funext z
    rw [← RCLike.normSq_eq_def', RCLike.normSq_apply]
  have hre : HasFDerivAt (fun z : K => RCLike.re z) (RCLike.reCLM : StrongDual ℝ K) 1 := by
    have h := (RCLike.reCLM : StrongDual ℝ K).hasFDerivAt (x := 1)
    rwa [RCLike.reCLM_apply] at h
  have him : HasFDerivAt (fun z : K => RCLike.im z) (RCLike.imCLM : StrongDual ℝ K) 1 := by
    have h := (RCLike.imCLM : StrongDual ℝ K).hasFDerivAt (x := 1)
    rwa [RCLike.imCLM_apply] at h
  have hsq := ((hre.mul hre).add (him.mul him)).congr_of_eventuallyEq
    (f₁ := fun z : K => ‖z‖ ^ 2) (Filter.Eventually.of_forall fun z => by
      simp only [Pi.add_apply, Pi.mul_apply]
      exact congrFun hn z)
  have hlog := hsq.log (by simp)
  refine hlog.congr_fderiv ?_
  ext w
  simp [RCLike.one_re, RCLike.one_im]
  ring

variable (F : Type u) [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

omit [NumberField F] [IsAffine G.X.left] in
theorem placeValue_one (v : InfinitePlace F) (s : AffineCoordinateRing F G.X) :
    placeValue F v s 1 = identityValue F s v := rfl

/-- If a regular function takes the value `1` at the identity, the derivative at the identity
of the logarithm of its archimedean norm is `Σ_v mult(v) · Re(D_X s)_v`. -/
theorem mfderiv_archimedeanLogRegular_one (s : AffineCoordinateRing F G.X)
    (hs : identityValue F s = 1)
    (X : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℝ) (AdelicGroupPoints.archimedeanLogRegular F G s) 1 X =
      ∑ v : InfinitePlace F, (v.mult : ℝ) * RCLike.re (regularDerivative F hsmooth X s v) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  have hone (v : InfinitePlace F) : placeValue F v s 1 = 1 := by
    rw [placeValue_one, hs]
    rfl
  have hcont (v : InfinitePlace F) : Continuous (placeValue F v s) :=
    (contMDiff_placeValue F hsmooth v s).continuous
  let g : InfiniteAdelicGroupPoints F G → ℝ := fun a =>
    ∑ v : InfinitePlace F, ((v.mult : ℝ) / 2) * Real.log (‖placeValue F v s a‖ ^ 2)
  have hU : {a : InfiniteAdelicGroupPoints F G | ∀ v, placeValue F v s a ≠ 0} ∈ 𝓝 1 := by
    have hopen : IsOpen {a : InfiniteAdelicGroupPoints F G | ∀ v, placeValue F v s a ≠ 0} := by
      have : {a : InfiniteAdelicGroupPoints F G | ∀ v, placeValue F v s a ≠ 0} =
          ⋂ v, (placeValue F v s) ⁻¹' {z | z ≠ 0} := by
        ext a
        simp
      rw [this]
      exact isOpen_iInter_of_finite fun v => (hcont v).isOpen_preimage _ isOpen_ne
    exact hopen.mem_nhds fun v => by rw [hone v]; exact one_ne_zero
  have heq : AdelicGroupPoints.archimedeanLogRegular F G s =ᶠ[𝓝 1] g := by
    filter_upwards [hU] with a ha
    change Real.log (∏ v : InfinitePlace F, ‖placeValue F v s a‖ ^ v.mult) = g a
    rw [Real.log_prod (fun v _ => pow_ne_zero _ (norm_ne_zero_iff.mpr (ha v)))]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hterm (v : InfinitePlace F) : HasMFDerivAt 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℝ)
      (fun a => ((v.mult : ℝ) / 2) * Real.log (‖placeValue F v s a‖ ^ 2)) 1
      (((v.mult : ℝ) / 2) • ((2 • (RCLike.reCLM : v.Completion →L[ℝ] ℝ)).comp
        (mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) (placeValue F v s) 1))) := by
    have hp := (((contMDiff_placeValue F hsmooth v s) 1).mdifferentiableAt
      (by simp)).hasMFDerivAt
    have hl : HasMFDerivAt 𝓘(ℝ, v.Completion) 𝓘(ℝ, ℝ) (fun z : v.Completion =>
        Real.log (‖z‖ ^ 2)) (placeValue F v s 1) (2 • (RCLike.reCLM : v.Completion →L[ℝ] ℝ)) := by
      rw [hone v]
      exact hasMFDerivAt_iff_hasFDerivAt.mpr (hasFDerivAt_log_norm_sq_one v.Completion)
    exact (hl.comp 1 hp).const_smul _
  have hsum := HasMFDerivAt.sum (t := Finset.univ) (fun v _ => hterm v)
  have hgdef : g = ∑ v : InfinitePlace F,
      (fun a => ((v.mult : ℝ) / 2) * Real.log (‖placeValue F v s a‖ ^ 2)) := by
    funext a
    simp only [g, Finset.sum_apply]
  have hg : HasMFDerivAt 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℝ) g 1
      (∑ v : InfinitePlace F, ((v.mult : ℝ) / 2) • ((2 • (RCLike.reCLM :
        v.Completion →L[ℝ] ℝ)).comp
        (mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) (placeValue F v s) 1))) := by
    rw [hgdef]
    exact hsum
  have hf := hg.congr_of_eventuallyEq heq
  refine (congrArg (fun L => L X) hf.mfderiv).trans ?_
  change ((∑ v : InfinitePlace F, ((v.mult : ℝ) / 2) • ((2 • (RCLike.reCLM :
      StrongDual ℝ v.Completion)).comp (mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion)
        (placeValue F v s) 1)) : TangentSpace 𝓘(ℝ, smoothModel F d)
          (1 : InfiniteAdelicGroupPoints F G) →L[ℝ] ℝ)) X = _
  rw [FunLike.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  have e1 : ((2 • (RCLike.reCLM : StrongDual ℝ v.Completion)) : v.Completion → ℝ) =
      fun z => 2 * RCLike.re z := by
    funext z
    simp [RCLike.reCLM_apply]
  let D : v.Completion := mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, v.Completion) (placeValue F v s) 1 X
  calc _ = (v.mult : ℝ) / 2 * ((2 • (RCLike.reCLM : StrongDual ℝ v.Completion)) D) := rfl
    _ = (v.mult : ℝ) / 2 * (2 * RCLike.re D) := congrArg _ (congrFun e1 D)
    _ = (v.mult : ℝ) * RCLike.re D := by ring

section Normalizer

open AdelicGroupPoints

omit [NumberField F] [IsAffine G.X.left] in
/-- A rational character takes the value `1` at the identity. -/
theorem identityValue_characterRegularFunction (ψ : rationalCharacters G) :
    identityValue F (G := G) (characterRegularFunction F G ψ) = 1 := by
  have h := characterUnits_val_eq_evaluation F G ψ (CommAlgCat.of F (InfiniteAdeleRing F)) 1
  rw [map_one, Units.val_one] at h
  exact h.symm

/-- The derivative at the identity of `m ↦ j(m)^{c ⊗ ψ}` along `X` is
`c · Σ_v mult(v) · Re(D_X (ψ ∘ j))_v`. -/
theorem mfderiv_parameterPower_tmul_one {H : GroupScheme (Spec (CommRingCat.of F))}
    (j : G ⟶ H) (c : ℂ) (ψ : rationalCharacters H)
    (X : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ)
        (fun m => parameterPower F H (c ⊗ₜ[ℤ] ψ) (map F G H j (ofInfinite F G m))) 1 X =
      c * ((∑ v : InfinitePlace F, (v.mult : ℝ) * RCLike.re (regularDerivative F hsmooth X
        (characterRegularFunction F G (characterRestrict j ψ)) v) : ℝ) : ℂ) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let s : AffineCoordinateRing F G.X := characterRegularFunction F G (characterRestrict j ψ)
  have hs : identityValue F s = 1 := identityValue_characterRegularFunction F _
  have hfun : (fun m => parameterPower F H (c ⊗ₜ[ℤ] ψ) (map F G H j (ofInfinite F G m))) =
      fun m => Complex.exp (c * (archimedeanLogRegular F G s m : ℂ)) := by
    funext m
    have h := characterLog_apply_ofInfinite F G (characterRestrict j ψ) m
    simp only [parameterPower, characterLog_map, complexParameterPairing_tmul]
    exact congrArg (fun r : ℝ => Complex.exp (c * (r : ℂ))) h
  have hne (v : InfinitePlace F) :
      G.affinePointEvaluation (CommAlgCat.of F (InfiniteAdeleRing F)) 1 s v ≠ 0 := by
    change identityValue F s v ≠ 0
    rw [hs]
    exact one_ne_zero
  have hL := ((contMDiffAt_archimedeanLogRegular F G hsmooth s 1 hne).mdifferentiableAt
    (by simp)).hasMFDerivAt
  have hL1 : archimedeanLogRegular F G s 1 = 0 := by
    change Real.log (∏ v : InfinitePlace F, ‖identityValue F s v‖ ^ v.mult) = 0
    rw [hs]
    have h1 (v : InfinitePlace F) : (1 : InfiniteAdeleRing F) v = (1 : v.Completion) := rfl
    simp [h1]
  have hE : HasFDerivAt (fun t : ℝ => Complex.exp (c * (t : ℂ))) (c • Complex.ofRealCLM)
      (archimedeanLogRegular F G s 1) := by
    have h := (Complex.ofRealCLM.hasFDerivAt (x := archimedeanLogRegular F G s 1)).const_mul
      c |>.cexp
    refine h.congr_fderiv ?_
    rw [hL1]
    ext
    simp
  have hcomp := (hasMFDerivAt_iff_hasFDerivAt.mpr hE).comp 1 hL
  rw [hfun]
  refine (congrArg (fun L => L X) hcomp.mfderiv).trans ?_
  have hA := mfderiv_archimedeanLogRegular_one F hsmooth s hs X
  change c * Complex.ofReal (mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℝ)
    (archimedeanLogRegular F G s) 1 X) = _
  rw [hA]

/-- The derivative at the identity of the normalizing factor `m ↦ δ_P(j(m))^{-1/2}` along `X`
is `-1/2 · Σ_v mult(v) · Re(D_X (det Ad_P ∘ j))_v`. -/
theorem mfderiv_halfModulus_one {P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine P.X.left]
    [LocallyOfFiniteType P.X.hom] (j : G ⟶ P)
    (X : letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
      letI := smoothChartedSpace F G hsmooth
      GroupLieAlgebra 𝓘(ℝ, smoothModel F d) (InfiniteAdelicGroupPoints F G)) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hsmooth
    mfderiv 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ)
        (fun m => parameterPower F P (-halfModulusParameter F P)
          (map F G P j (ofInfinite F G m))) 1 X =
      (-1 / 2 : ℂ) * ((∑ v : InfinitePlace F, (v.mult : ℝ) * RCLike.re (regularDerivative F
        hsmooth X (characterRegularFunction F G
          (characterRestrict j (Lie.adjointDeterminantCharacter P))) v) : ℝ) : ℂ) := by
  have h : -halfModulusParameter F P =
      (-1 / 2 : ℂ) ⊗ₜ[ℤ] Lie.adjointDeterminantCharacter P := by
    rw [halfModulusParameter, ← TensorProduct.neg_tmul]
    norm_num
  rw [h]
  exact mfderiv_parameterPower_tmul_one F hsmooth j _ _ X

end Normalizer

end Langlands.Global.InfiniteAdelicGroupPoints
