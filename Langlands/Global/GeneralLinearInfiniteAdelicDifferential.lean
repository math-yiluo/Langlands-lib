import Langlands.Automorphic.GroupSchemeDifferential
import Langlands.Global.GeneralLinearInfiniteAdelicManifold
import Langlands.Global.ArchimedeanDifferentialGeometry
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-! # The original general-linear differential and the actual adelic tangent -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Manifold

section Naturality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']
  [LieGroup J ∞ G']

/-- The actual orbit derivative is natural under a smooth group homomorphism. -/
theorem groupDirectionalValue_comp_mulHom (e : G →* G')
    (he : ContMDiff I J ∞ e) (X : GroupLieAlgebra I G)
    {f : G' → ℂ} (hf : ContMDiff J 𝓘(ℝ, ℂ) ∞ f) (g : G) :
    groupDirectionalValue I X (f ∘ e) g =
      groupDirectionalValue J (mfderiv I J e 1 X) f (e g) := by
  have hL : ContMDiff J J ∞ (fun h : G' => e g * h) :=
    contMDiff_const.mul contMDiff_id
  have horbit : (fun h : G => (f ∘ e) (g * h)) =
      (fun h : G' => f (e g * h)) ∘ e := by
    funext h
    simp only [Function.comp_apply, map_mul]
  unfold groupDirectionalValue
  rw [horbit]
  exact mvfderiv_comp_apply_of_eq (I := J) (I' := I) (1 : G)
    ((hf.comp hL).mdifferentiableAt (by simp)) (he.mdifferentiableAt (by simp))
    e.map_one X

end Naturality

section Units

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

/-- In the original units atlas, the derivative of the value chart is identity. -/
theorem units_mfderiv_val (g : Rˣ) :
    mfderiv 𝓘(ℝ, R) 𝓘(ℝ, R) (Units.val : Rˣ → R) g =
      ContinuousLinearMap.id ℝ R := by
  exact mfderiv_extChartAt_self (I := 𝓘(ℝ, R)) (x := g)

/-- The actual invariant tangent of a units group is multiplication in the algebra. -/
theorem units_mulInvariantVectorField (X : R) (g : Rˣ) :
    mulInvariantVectorField (I := 𝓘(ℝ, R)) X g = (g : R) * X := by
  let L : R →L[ℝ] R := (ContinuousLinearMap.mul ℝ R) (g : R)
  have hL : ContMDiff 𝓘(ℝ, R) 𝓘(ℝ, R) ∞ (fun h : Rˣ => g * h) :=
    contMDiff_const.mul contMDiff_id
  have heq : (Units.val : Rˣ → R) ∘ (fun h : Rˣ => g * h) =
      (L : R → R) ∘ (Units.val : Rˣ → R) := rfl
  have h₁ := mfderiv_comp (I := 𝓘(ℝ, R)) (I' := 𝓘(ℝ, R)) (I'' := 𝓘(ℝ, R))
    (1 : Rˣ) ((Units.contMDiff_val (𝕜 := ℝ) (n := ∞)).mdifferentiableAt (by simp))
    (hL.mdifferentiableAt (by simp))
  have h₂ := mfderiv_comp (I := 𝓘(ℝ, R)) (I' := 𝓘(ℝ, R)) (I'' := 𝓘(ℝ, R))
    (1 : Rˣ) (((L.contDiff (n := ∞)).contMDiff).mdifferentiableAt (by simp))
    ((Units.contMDiff_val (𝕜 := ℝ) (n := ∞)).mdifferentiableAt (by simp))
  rw [heq] at h₁
  rw [h₂] at h₁
  simp only [units_mfderiv_val, mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at h₁
  exact congrArg (fun D : R →L[ℝ] R => D X) h₁.symm

/-- Orbit differentiation in the units atlas uses the usual algebra direction. -/
theorem units_groupDirectionalValue (X : R) {f : Rˣ → ℂ}
    (hf : ContMDiff 𝓘(ℝ, R) 𝓘(ℝ, ℂ) ∞ f) (g : Rˣ) :
    groupDirectionalValue 𝓘(ℝ, R) X f g =
      mvfderiv 𝓘(ℝ, R) f g ((g : R) * X) := by
  rw [groupDirectionalValue_eq_invariant _ X hf g, units_mulInvariantVectorField]

end Units

end Langlands.Geometry.Manifold

namespace Langlands.Global.GeneralLinearGroupPoints

open Langlands.Geometry.Manifold

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GLG" =>
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance differentialGeneralLinearIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

variable {d : ℕ}

/-- Differentiate the original actual-point/mixed-coordinate diffeomorphism at one. -/
def infiniteRealLieAlgebraEquiv
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := InfiniteAdelicGroupPoints.smoothChartedSpace F GLG hsmooth
    GroupLieAlgebra 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d)
      (InfiniteAdelicGroupPoints F GLG) ≃ₗ[ℝ] ArchimedeanGL.RealLieAlgebra F n := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := InfiniteAdelicGroupPoints.smoothChartedSpace F GLG hsmooth
  exact ((infiniteDiffeomorph F n hsmooth).mfderivToContinuousLinearEquiv
    (by simp) 1).toLinearEquiv.trans (ArchimedeanGL.realLieAlgebraToMatrix F n).symm

theorem infiniteRealLieAlgebraEquiv_apply
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom)
    (X : InfiniteAdelicGroupPoints.smoothModel F d) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := InfiniteAdelicGroupPoints.smoothChartedSpace F GLG hsmooth
    ArchimedeanGL.realLieAlgebraToMatrix F n (infiniteRealLieAlgebraEquiv F n hsmooth X) =
      mfderiv 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d)
        𝓘(ℝ, ArchimedeanMatrix F n) (infiniteDiffeomorph F n hsmooth) 1 X := rfl

/-- Under the original maps, actual orbit differentiation is the existing
mixed-coordinate matrix differential. -/
theorem infinite_groupDirectionalValue
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom)
    (X : InfiniteAdelicGroupPoints.smoothModel F d)
    (f : ArchimedeanGL.SmoothFunctions F n) (g : InfiniteAdelicGroupPoints F GLG) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := InfiniteAdelicGroupPoints.smoothChartedSpace F GLG hsmooth
    groupDirectionalValue 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) X
      (fun h => f.val (infiniteHomeomorph F n h)) g =
      (ArchimedeanGL.smoothDifferential F n (infiniteRealLieAlgebraEquiv F n hsmooth X) f).val
        (infiniteHomeomorph F n g) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := InfiniteAdelicGroupPoints.smoothChartedSpace F GLG hsmooth
  let e := GroupScheme.GeneralLinear.coefficientCoordinatesEquiv
    (Fin n) (CommRingCat.of F) (CommAlgCat.of F (InfiniteAdeleRing F))
    (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  let fM : ArchimedeanGL F n → ℂ :=
    fun h => f.val ((archimedeanGLCoordinates F n).symm h)
  have he : ContMDiff 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d)
      𝓘(ℝ, ArchimedeanMatrix F n) ∞ e :=
    (infiniteDiffeomorph F n hsmooth).contMDiff_toFun
  have hf : ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, ℂ) ∞ fM := f.property
  have horiginal : (fun h => f.val (infiniteHomeomorph F n h)) = fM ∘ e := by
    funext h
    change f.val (infiniteHomeomorph F n h) =
      f.val ((archimedeanGLCoordinates F n).symm
        (archimedeanGLCoordinates F n (infiniteHomeomorph F n h)))
    rw [ContinuousMulEquiv.symm_apply_apply]
  rw [horiginal]
  refine (groupDirectionalValue_comp_mulHom e.toMonoidHom he X hf g).trans ?_
  refine (units_groupDirectionalValue _ hf (e g)).trans ?_
  rw [ArchimedeanGL.smoothDifferential_eq_mfderiv]
  rfl

/-- The unchanged original smooth-function equivalence intertwines the actual
adelic differential and the original general-linear differential. -/
theorem plotSmoothGeneralLinearEquiv_differential
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom)
    (X : InfiniteAdelicGroupPoints.smoothModel F d)
    (f : (GLG).plotSmoothFunctions (CommAlgCat.of F (InfiniteAdeleRing F))
      (B := mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := InfiniteAdelicGroupPoints.smoothChartedSpace F GLG hsmooth
    plotSmoothGeneralLinearEquiv F n
        (InfiniteAdelicGroupPoints.plotSmoothDifferential F GLG hsmooth X f) =
      ArchimedeanGL.smoothDifferential F n (infiniteRealLieAlgebraEquiv F n hsmooth X)
        (plotSmoothGeneralLinearEquiv F n f) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := InfiniteAdelicGroupPoints.smoothChartedSpace F GLG hsmooth
  apply Subtype.ext
  funext x
  change groupDirectionalValue 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) X f.val
    ((infiniteHomeomorph F n).symm x) = _
  simpa only [plotSmoothGeneralLinearEquiv_apply, ContinuousMulEquiv.symm_apply_apply,
    ContinuousMulEquiv.apply_symm_apply] using
    infinite_groupDirectionalValue F n hsmooth X (plotSmoothGeneralLinearEquiv F n f)
      ((infiniteHomeomorph F n).symm x)

/-- The actual identity tangent for the canonical reductive atlas is the
original general-linear real Lie algebra, without a supplied identification. -/
def reductiveInfiniteRealLieAlgebraEquiv :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := InfiniteAdelicGroupPoints.reductiveChartedSpace F GLG
      (GroupScheme.isConnectedReductive_generalLinear F (Fin n))
    GroupLieAlgebra
      𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F
        (GroupScheme.isConnectedReductive_generalLinear F (Fin n)).smoothDimension)
      (InfiniteAdelicGroupPoints F GLG) ≃ₗ[ℝ] ArchimedeanGL.RealLieAlgebra F n := by
  letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  exact infiniteRealLieAlgebraEquiv F n
    (GroupScheme.isConnectedReductive_generalLinear F (Fin n)).smoothDimension_spec

/-- The canonical reductive differential agrees with the original differential
under the original smooth-function equivalence. -/
theorem plotSmoothGeneralLinearEquiv_reductiveDifferential
    (X : InfiniteAdelicGroupPoints.smoothModel F
      (GroupScheme.isConnectedReductive_generalLinear F (Fin n)).smoothDimension)
    (f : (GLG).plotSmoothFunctions (CommAlgCat.of F (InfiniteAdeleRing F))
      (B := mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom) :
    let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := InfiniteAdelicGroupPoints.reductiveChartedSpace F GLG
      (GroupScheme.isConnectedReductive_generalLinear F (Fin n))
    plotSmoothGeneralLinearEquiv F n
        (InfiniteAdelicGroupPoints.reductiveRealPlotSmoothDifferential F GLG
          (GroupScheme.isConnectedReductive_generalLinear F (Fin n)) X f) =
      ArchimedeanGL.smoothDifferential F n (reductiveInfiniteRealLieAlgebraEquiv F n X)
        (plotSmoothGeneralLinearEquiv F n f) :=
  plotSmoothGeneralLinearEquiv_differential F n
    (GroupScheme.isConnectedReductive_generalLinear F (Fin n)).smoothDimension_spec X f

end Langlands.Global.GeneralLinearGroupPoints
