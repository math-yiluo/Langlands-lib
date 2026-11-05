import Langlands.Global.ReductiveInfiniteAdelicManifold
import Langlands.GroupScheme.GeneralLinearSmoothFunctions
import Langlands.GroupScheme.Reductive.GeneralLinear

/-! # The original general-linear manifold and the infinite adelic atlas -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Global.GeneralLinearGroupPoints

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "GLG" =>
  GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)

local instance manifoldGeneralLinearIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

variable {d : ℕ}
  {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- Incoming smoothness in the specified adelic atlas is exactly smoothness
after the original matrix coordinate map. -/
theorem contMDiff_infinite_iff_matrixCoordinates
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom)
    (p : M → InfiniteAdelicGroupPoints F GLG) :
    let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := InfiniteAdelicGroupPoints.smoothChartedSpace F GLG hsmooth
    ContMDiff I 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) ∞ p ↔
      ContMDiff I 𝓘(ℝ, ArchimedeanMatrix F n) ∞
        (fun x => archimedeanGLCoordinates F n (infiniteHomeomorph F n (p x))) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := InfiniteAdelicGroupPoints.smoothChartedSpace F GLG hsmooth
  exact (InfiniteAdelicGroupPoints.contMDiff_iff_coordinateSmooth F GLG I hsmooth p).trans
    (GroupScheme.GeneralLinear.coordinateSmooth_iff_contMDiff
      (Fin n) (CommRingCat.of F) (CommAlgCat.of F (InfiniteAdeleRing F))
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom I p)

/-- The existing actual-point and mixed-coordinate maps form a diffeomorphism
to the original matrix-units atlas. -/
def infiniteDiffeomorph
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := InfiniteAdelicGroupPoints.smoothChartedSpace F GLG hsmooth
    Diffeomorph 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d)
      𝓘(ℝ, ArchimedeanMatrix F n)
      (InfiniteAdelicGroupPoints F GLG) (ArchimedeanGL F n) ∞ := by
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := InfiniteAdelicGroupPoints.smoothChartedSpace F GLG hsmooth
  let e := GroupScheme.GeneralLinear.coefficientCoordinatesEquiv
    (Fin n) (CommRingCat.of F) (CommAlgCat.of F (InfiniteAdeleRing F))
    (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  refine
    { toEquiv := e.toEquiv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · exact (contMDiff_infinite_iff_matrixCoordinates F n
      𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) hsmooth id).mp contMDiff_id
  · apply (contMDiff_infinite_iff_matrixCoordinates F n
      𝓘(ℝ, ArchimedeanMatrix F n) hsmooth e.symm).mpr
    change ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, ArchimedeanMatrix F n) ∞
      (fun x => e (e.symm x))
    simp only [MulEquiv.apply_symm_apply]
    exact contMDiff_id

theorem infiniteDiffeomorph_toEquiv
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) :
    let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := InfiniteAdelicGroupPoints.smoothChartedSpace F GLG hsmooth
    (infiniteDiffeomorph F n hsmooth).toEquiv =
      ((infiniteHomeomorph F n).trans (archimedeanGLCoordinates F n)).toEquiv := rfl

/-- Ordinary smoothness on the constructed actual-point manifold is precisely
membership in the original completion-based smooth-function space. -/
theorem contMDiff_iff_mem_smoothFunctions
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom)
    (f : InfiniteAdelicGroupPoints F GLG → ℂ) :
    let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := InfiniteAdelicGroupPoints.smoothChartedSpace F GLG hsmooth
    ContMDiff 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) 𝓘(ℝ, ℂ) ∞ f ↔
      (fun x => f ((infiniteHomeomorph F n).symm x)) ∈
        ArchimedeanGL.smoothFunctions F n := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := InfiniteAdelicGroupPoints.smoothChartedSpace F GLG hsmooth
  exact ((infiniteDiffeomorph F n hsmooth).symm.contMDiff_comp_diffeomorph_iff
    (f := f) le_rfl).symm

/-- The canonical connected-reductive charts compare with the original matrix
manifold without a separate dimension or analytic premise. -/
def reductiveInfiniteDiffeomorph :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := InfiniteAdelicGroupPoints.reductiveChartedSpace F GLG
      (GroupScheme.isConnectedReductive_generalLinear F (Fin n))
    Diffeomorph
      𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F
        (GroupScheme.isConnectedReductive_generalLinear F (Fin n)).smoothDimension)
      𝓘(ℝ, ArchimedeanMatrix F n)
      (InfiniteAdelicGroupPoints F GLG) (ArchimedeanGL F n) ∞ := by
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  exact infiniteDiffeomorph F n
    (GroupScheme.isConnectedReductive_generalLinear F (Fin n)).smoothDimension_spec

end Langlands.Global.GeneralLinearGroupPoints
