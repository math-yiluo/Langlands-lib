import Langlands.Geometry.Manifold.HomeomorphTransport
import Langlands.GroupScheme.General.SmoothAffinePointLieGroup
import Langlands.GroupScheme.AffinePointBaseChangeSmooth

/-! # The actual affine point manifold through algebraic base change -/

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj Manifold ContDiff

namespace Langlands.GroupScheme.General

open Langlands.AlgebraicGeometry.PointTopology
open Langlands.AlgebraicGeometry.PointManifold.General
open Langlands.Geometry.Manifold

set_option backward.isDefEq.respectTransparency false

variable (C k : Type u) [CommRing C] [RCLike k] [Algebra C k]
  (G : GroupScheme (Spec (CommRingCat.of C))) [IsAffine G.X.left]

private instance baseChanged_isAffine :
    IsAffine ((GroupScheme.baseChange (Spec.algebraMap C k)).obj G).X.left := by
  change IsAffine (pullback G.X.hom (Spec.algebraMap C k))
  infer_instance

local instance originalPointTopology :
    TopologicalSpace (G.affinePoints (CommAlgCat.of C k)) :=
  G.affinePointsTopologicalSpace (CommAlgCat.of C k)

local instance baseChangedPointTopology :
    TopologicalSpace
      (((GroupScheme.baseChange (Spec.algebraMap C k)).obj G).affinePoints
        (CommAlgCat.of k k)) :=
  affinePointsTopologicalSpace
    ((GroupScheme.baseChange (Spec.algebraMap C k)).obj G) (CommAlgCat.of k k)

/-- Actual scalar extension followed by the identity comparison of the two
relative-morphism point carriers, with their existing evaluation topologies. -/
def affineBaseChangePointHomeomorph :
    G.affinePoints (CommAlgCat.of C k) ≃ₜ
      RingPoint k ((GroupScheme.baseChange (Spec.algebraMap C k)).obj G).X k :=
  (affinePointsBaseChangeContinuousMulEquiv C k k G).toHomeomorph.trans
    (affinePointsRingPointHomeomorph
      ((GroupScheme.baseChange (Spec.algebraMap C k)).obj G) (CommAlgCat.of k k))

omit [IsAffine G.X.left] in
/-- Constant-relative-dimension smoothness is preserved by the actual pullback. -/
theorem affineBaseChange_smooth {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    SmoothOfRelativeDimension d
      ((GroupScheme.baseChange (Spec.algebraMap C k)).obj G).X.hom := by
  change SmoothOfRelativeDimension d (pullback.snd G.X.hom (Spec.algebraMap C k))
  exact MorphismProperty.pullback_snd G.X.hom (Spec.algebraMap C k) hsmooth

variable {d : ℕ}

/-- Pull exactly the chosen General affine charts back to the original G(k). -/
@[instance_reducible]
def affineBaseChangeChartedSpace
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    ChartedSpace (Fin d → k) (G.affinePoints (CommAlgCat.of C k)) := by
  letI := smoothAffineChartedSpace (affineBaseChange_smooth C k G hsmooth)
  exact pullbackChartedSpace (H := Fin d → k) (affineBaseChangePointHomeomorph C k G)

/-- The original G(k) topology carries the algebraically constructed real manifold. -/
theorem affineBaseChangeIsManifold
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := affineBaseChangeChartedSpace C k G hsmooth
    IsManifold 𝓘(ℝ, Fin d → k) ∞ (G.affinePoints (CommAlgCat.of C k)) := by
  let := smoothAffineChartedSpace (affineBaseChange_smooth C k G hsmooth)
  let : IsManifold 𝓘(ℝ, Fin d → k) ∞
      (RingPoint k ((GroupScheme.baseChange (Spec.algebraMap C k)).obj G).X k) :=
    smoothAffineIsManifold (affineBaseChange_smooth C k G hsmooth)
  exact pullbackIsManifold 𝓘(ℝ, Fin d → k) ∞ (affineBaseChangePointHomeomorph C k G)

/-- The literal scalar-extension comparison is a diffeomorphism to the exact
chosen General charts of the base-changed affine scheme. -/
def affineBaseChangeDiffeomorph
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := smoothAffineChartedSpace (affineBaseChange_smooth C k G hsmooth)
    letI := affineBaseChangeChartedSpace C k G hsmooth
    Diffeomorph 𝓘(ℝ, Fin d → k) 𝓘(ℝ, Fin d → k)
      (G.affinePoints (CommAlgCat.of C k))
      (RingPoint k ((GroupScheme.baseChange (Spec.algebraMap C k)).obj G).X k) ∞ := by
  letI := smoothAffineChartedSpace (affineBaseChange_smooth C k G hsmooth)
  exact pullbackDiffeomorph 𝓘(ℝ, Fin d → k) ∞ (affineBaseChangePointHomeomorph C k G)

/-- No map is replaced by the manifold transport. -/
theorem affineBaseChangeDiffeomorph_toEquiv
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := smoothAffineChartedSpace (affineBaseChange_smooth C k G hsmooth)
    letI := affineBaseChangeChartedSpace C k G hsmooth
    (affineBaseChangeDiffeomorph C k G hsmooth).toEquiv =
      (affineBaseChangePointHomeomorph C k G).toEquiv := rfl

section Families

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]

/-- Smoothness on the actual constructed manifold is precisely the original
coordinate criterion, tested before scalar extension. -/
theorem affineBaseChange_contMDiff_iff_coordinateSmooth
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (p : M → G.affinePoints (CommAlgCat.of C k)) :
    letI := affineBaseChangeChartedSpace C k G hsmooth
    ContMDiff I 𝓘(ℝ, Fin d → k) ∞ p ↔
      G.CoordinateSmooth (CommAlgCat.of C k) (RingHom.id k) I p := by
  let := smoothAffineChartedSpace (affineBaseChange_smooth C k G hsmooth)
  exact (contMDiff_pullback_iff 𝓘(ℝ, Fin d → k) ∞ I
    (affineBaseChangePointHomeomorph C k G) p).trans
    ((smoothAffine_contMDiff_iff_coordinateSmooth
      ((GroupScheme.baseChange (Spec.algebraMap C k)).obj G) I
      (affineBaseChange_smooth C k G hsmooth)
      (fun t => affinePointsBaseChangeMulEquiv C k k G (p t))).trans
        (coordinateSmooth_baseChange_iff C k k G (RingHom.id k) I p))

end Families

/-- The constructed charts make the literal original point group a real Lie group. -/
theorem affineBaseChangeLieGroup
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := affineBaseChangeChartedSpace C k G hsmooth
    LieGroup 𝓘(ℝ, Fin d → k) ∞ (G.affinePoints (CommAlgCat.of C k)) := by
  let := affineBaseChangeChartedSpace C k G hsmooth
  let : IsManifold 𝓘(ℝ, Fin d → k) ∞ (G.affinePoints (CommAlgCat.of C k)) :=
    affineBaseChangeIsManifold C k G hsmooth
  refine { toIsManifold := inferInstance, contMDiff_mul := ?_, contMDiff_inv := ?_ }
  · apply (affineBaseChange_contMDiff_iff_coordinateSmooth C k G
      (𝓘(ℝ, Fin d → k).prod 𝓘(ℝ, Fin d → k)) hsmooth _).mpr
    apply CoordinateSmooth.mul G (CommAlgCat.of C k) (RingHom.id k)
    · exact (affineBaseChange_contMDiff_iff_coordinateSmooth C k G
        (𝓘(ℝ, Fin d → k).prod 𝓘(ℝ, Fin d → k)) hsmooth _).mp contMDiff_fst
    · exact (affineBaseChange_contMDiff_iff_coordinateSmooth C k G
        (𝓘(ℝ, Fin d → k).prod 𝓘(ℝ, Fin d → k)) hsmooth _).mp contMDiff_snd
  · apply (affineBaseChange_contMDiff_iff_coordinateSmooth C k G
      𝓘(ℝ, Fin d → k) hsmooth _).mpr
    exact ((affineBaseChange_contMDiff_iff_coordinateSmooth C k G
      𝓘(ℝ, Fin d → k) hsmooth _).mp contMDiff_id).inv

/-- Every original global-function value is smooth on the constructed manifold. -/
theorem affineBaseChange_contMDiff_evaluation
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (a : AffineCoordinateRing C G.X) :
    letI := affineBaseChangeChartedSpace C k G hsmooth
    ContMDiff 𝓘(ℝ, Fin d → k) 𝓘(ℝ, k) ∞
      (fun p : G.affinePoints (CommAlgCat.of C k) =>
        G.affinePointEvaluation (CommAlgCat.of C k) p a) := by
  let := affineBaseChangeChartedSpace C k G hsmooth
  exact ((affineBaseChange_contMDiff_iff_coordinateSmooth C k G
    𝓘(ℝ, Fin d → k) hsmooth _).mp contMDiff_id) a

end Langlands.GroupScheme.General
