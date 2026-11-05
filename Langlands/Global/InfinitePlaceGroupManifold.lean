import Langlands.Global.InfiniteAdelicGroupProduct
import Langlands.Global.InfiniteCompletionRCLike
import Langlands.GroupScheme.General.AffinePointBaseChangeManifold
import Mathlib.Topology.Instances.RealVectorSpace

/-! # The constructed manifold of actual infinite-place group points -/

noncomputable section

universe u v w z

open CategoryTheory AlgebraicGeometry NumberField
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.Global.InfinitePlaceGroupPoints

set_option backward.isDefEq.respectTransparency false

/-- The published compatible completion structure, pinned as a named choice.
Its normed field is definitionally the original completion normed field. -/
@[instance_reducible]
def completionRCLike (F : Type u) [Field F] (v : InfinitePlace F) : RCLike v.Completion := by
  letI := v.completion_isRCLikeNormedField
  exact IsRCLikeNormedField.rclike v.Completion

variable (F : Type u) [Field F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  (v : InfinitePlace F) {d : ℕ}

/-- The original local point group with the exact algebraic base-change charts. -/
@[instance_reducible]
def smoothChartedSpace (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    ChartedSpace (Fin d → v.Completion) (InfinitePlaceGroupPoints F G v) := by
  letI := completionRCLike F v
  exact GroupScheme.General.affineBaseChangeChartedSpace F v.Completion G hsmooth

/-- The original local evaluation topology supports the constructed real manifold. -/
theorem smoothIsManifold (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    let := completionRCLike F v
    let := smoothChartedSpace F G v hsmooth
    IsManifold 𝓘(ℝ, Fin d → v.Completion) ∞ (InfinitePlaceGroupPoints F G v) := by
  let := completionRCLike F v
  exact GroupScheme.General.affineBaseChangeIsManifold F v.Completion G hsmooth

/-- The same actual local point group and charts form a real Lie group. -/
theorem smoothLieGroup (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    let := completionRCLike F v
    let := smoothChartedSpace F G v hsmooth
    LieGroup 𝓘(ℝ, Fin d → v.Completion) ∞ (InfinitePlaceGroupPoints F G v) := by
  let := completionRCLike F v
  exact GroupScheme.General.affineBaseChangeLieGroup F v.Completion G hsmooth

variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type w} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type z} [TopologicalSpace M] [ChartedSpace H M]

/-- Ordinary manifold smoothness is the original completion-valued criterion. -/
theorem contMDiff_iff_coordinateSmooth
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (p : M → InfinitePlaceGroupPoints F G v) :
    let := completionRCLike F v
    let := smoothChartedSpace F G v hsmooth
    ContMDiff I 𝓘(ℝ, Fin d → v.Completion) ∞ p ↔
      G.CoordinateSmooth (CommAlgCat.of F v.Completion)
        (RingHom.id v.Completion) I p := by
  let := completionRCLike F v
  exact GroupScheme.General.affineBaseChange_contMDiff_iff_coordinateSmooth
    F v.Completion G I hsmooth p

/-- At a real place, the criterion agrees with the specified actual map to ℝ. -/
theorem contMDiff_iff_realCoordinates (hv : IsReal v)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (p : M → InfinitePlaceGroupPoints F G v) :
    let := completionRCLike F v
    let := smoothChartedSpace F G v hsmooth
    ContMDiff I 𝓘(ℝ, Fin d → v.Completion) ∞ p ↔
      G.CoordinateSmooth (CommAlgCat.of F v.Completion)
        (B := ℝ) (ringEquivRealOfIsReal hv).toRingHom I p := by
  let := completionRCLike F v
  let := smoothChartedSpace F G v hsmooth
  apply (contMDiff_iff_coordinateSmooth F G v I hsmooth p).trans
  apply forall_congr'
  intro a
  let L : v.Completion ≃L[ℝ] ℝ :=
    (ringEquivRealOfIsReal hv).toAddEquiv.toRealLinearEquiv
      (isometryEquivRealOfIsReal hv).continuous
      (isometryEquivRealOfIsReal hv).symm.continuous
  exact (L.toDiffeomorph.contMDiff_diffeomorph_comp_iff
    (f := fun t => G.affinePointEvaluation (CommAlgCat.of F v.Completion) (p t) a)
    le_rfl).symm

/-- At a complex place, the criterion agrees with the specified actual map to ℂ,
with real differentiability on both sides. -/
theorem contMDiff_iff_complexCoordinates (hv : IsComplex v)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (p : M → InfinitePlaceGroupPoints F G v) :
    let := completionRCLike F v
    let := smoothChartedSpace F G v hsmooth
    ContMDiff I 𝓘(ℝ, Fin d → v.Completion) ∞ p ↔
      G.CoordinateSmooth (CommAlgCat.of F v.Completion)
        (B := ℂ) (ringEquivComplexOfIsComplex hv).toRingHom I p := by
  let := completionRCLike F v
  let := smoothChartedSpace F G v hsmooth
  apply (contMDiff_iff_coordinateSmooth F G v I hsmooth p).trans
  apply forall_congr'
  intro a
  let L : v.Completion ≃L[ℝ] ℂ :=
    (ringEquivComplexOfIsComplex hv).toAddEquiv.toRealLinearEquiv
      (isometryEquivComplexOfIsComplex hv).continuous
      (isometryEquivComplexOfIsComplex hv).symm.continuous
  exact (L.toDiffeomorph.contMDiff_diffeomorph_comp_iff
    (f := fun t => G.affinePointEvaluation (CommAlgCat.of F v.Completion) (p t) a)
    le_rfl).symm

end Langlands.Global.InfinitePlaceGroupPoints
