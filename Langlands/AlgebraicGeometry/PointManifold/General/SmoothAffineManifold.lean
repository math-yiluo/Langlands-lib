import Langlands.AlgebraicGeometry.PointManifold.General.RegularChartExistenceProof
import Langlands.AlgebraicGeometry.PointManifold.General.RegularAtlasFunctoriality

/-! # The universe-general real smooth manifold of actual smooth affine points

The atlas is chosen from the proved algebraic chart-existence theorem. Its
charted space uses the existing regular-function evaluation topology.
-/

noncomputable section

universe u v w z

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped Manifold ContDiff

namespace Langlands.AlgebraicGeometry.PointManifold.General

open PointTopology

variable {k : Type u} [RCLike k]
variable {X : Over (Spec (CommRingCat.of k))} [IsAffine X.left] {d : ℕ}

/-- Choose the algebraically supplied atlas, retaining the existing point topology. -/
def smoothAffineRegularAtlas
    (hsmooth : SmoothOfRelativeDimension d X.hom) : RegularAtlas k X d :=
  Classical.choice (regularChartExistence k X d hsmooth)

/-- The actual real-point specialization of the chosen atlas. -/
abbrev realSmoothAffineRegularAtlas
    (X : Over (Spec (CommRingCat.of ℝ))) [IsAffine X.left] (d : ℕ)
    (hsmooth : SmoothOfRelativeDimension d X.hom) : RegularAtlas ℝ X d :=
  smoothAffineRegularAtlas hsmooth

/-- The actual complex-point specialization, with real model dimension `2 * d`. -/
abbrev complexSmoothAffineRegularAtlas
    (X : Over (Spec (CommRingCat.of ℂ))) [IsAffine X.left] (d : ℕ)
    (hsmooth : SmoothOfRelativeDimension d X.hom) : RegularAtlas ℂ X d :=
  smoothAffineRegularAtlas hsmooth

/-- The named charted space on actual points. No new topology is introduced. -/
@[instance_reducible] def smoothAffineChartedSpace
    (hsmooth : SmoothOfRelativeDimension d X.hom) :
    ChartedSpace (Fin d → k) (RingPoint k X k) :=
  (smoothAffineRegularAtlas hsmooth).chartedSpace

/-- The named real-point charted space on the actual carrier. -/
abbrev realSmoothAffineChartedSpace
    (X : Over (Spec (CommRingCat.of ℝ))) [IsAffine X.left] (d : ℕ)
    (hsmooth : SmoothOfRelativeDimension d X.hom) :
    ChartedSpace (Fin d → ℝ) (RingPoint ℝ X ℝ) :=
  smoothAffineChartedSpace hsmooth

/-- The named complex-point charted space, viewed as a real charted space. -/
abbrev complexSmoothAffineChartedSpace
    (X : Over (Spec (CommRingCat.of ℂ))) [IsAffine X.left] (d : ℕ)
    (hsmooth : SmoothOfRelativeDimension d X.hom) :
    ChartedSpace (Fin d → ℂ) (RingPoint ℂ X ℂ) :=
  smoothAffineChartedSpace hsmooth

/-- With the constructed charts installed, the point topology is exactly the
topology induced by all global regular-function evaluations. -/
theorem smoothAffine_topology_eq_evaluation
    (hsmooth : SmoothOfRelativeDimension d X.hom) :
    letI := smoothAffineChartedSpace hsmooth
    (inferInstance : TopologicalSpace (RingPoint k X k)) =
      TopologicalSpace.induced
        (fun p : RingPoint k X k => fun a : AffineCoordinateRing k X =>
          regularEvaluation p a) inferInstance := by
  change TopologicalSpace.induced (affineSchemePointEquiv k X k)
    (TopologicalSpace.induced AlgPoint.evaluation inferInstance) = _
  exact induced_compose

/-- Analytic compatibility upgrades the algebraically chosen atlas to a manifold. -/
theorem smoothAffineIsManifold
    (hsmooth : SmoothOfRelativeDimension d X.hom) :
    letI := smoothAffineChartedSpace hsmooth
    IsManifold 𝓘(ℝ, Fin d → k) ∞ (RingPoint k X k) :=
  (smoothAffineRegularAtlas hsmooth).isManifold

/-- The real-point manifold has real model dimension `d`. -/
theorem realSmoothAffineIsManifold
    (X : Over (Spec (CommRingCat.of ℝ))) [IsAffine X.left] (d : ℕ)
    (hsmooth : SmoothOfRelativeDimension d X.hom) :
    letI := realSmoothAffineChartedSpace X d hsmooth
    IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ (RingPoint ℝ X ℝ) :=
  smoothAffineIsManifold hsmooth

/-- The complex-point manifold has real model dimension `2 * d`. -/
theorem complexSmoothAffineIsManifold
    (X : Over (Spec (CommRingCat.of ℂ))) [IsAffine X.left] (d : ℕ)
    (hsmooth : SmoothOfRelativeDimension d X.hom) :
    letI := complexSmoothAffineChartedSpace X d hsmooth
    IsManifold 𝓘(ℝ, Fin d → ℂ) ∞ (RingPoint ℂ X ℂ) :=
  smoothAffineIsManifold hsmooth

/-- Every global regular function is smooth for the chosen structure. -/
theorem smoothAffine_contMDiff_regularEvaluation
    (hsmooth : SmoothOfRelativeDimension d X.hom)
    (a : AffineCoordinateRing k X) :
    letI := smoothAffineChartedSpace hsmooth
    ContMDiff 𝓘(ℝ, Fin d → k) 𝓘(ℝ, k) ∞
      (fun p : RingPoint k X k => regularEvaluation p a) :=
  (smoothAffineRegularAtlas hsmooth).contMDiff_regularEvaluation a

variable {Y : Over (Spec (CommRingCat.of k))} [IsAffine Y.left] {e : ℕ}

/-- Actual relative morphisms are smooth between the chosen structures. -/
theorem smoothAffine_contMDiff_postcomp
    (hX : SmoothOfRelativeDimension d X.hom)
    (hY : SmoothOfRelativeDimension e Y.hom) (f : X ⟶ Y) :
    @ContMDiff ℝ _ (Fin d → k) _ _ (Fin d → k) _ 𝓘(ℝ, Fin d → k)
      (RingPoint k X k) _ (smoothAffineChartedSpace hX)
      (Fin e → k) _ _ (Fin e → k) _ 𝓘(ℝ, Fin e → k)
      (RingPoint k Y k) _ (smoothAffineChartedSpace hY) ∞ (fun p => p ≫ f) :=
  (smoothAffineRegularAtlas hX).contMDiff_postcomp (smoothAffineRegularAtlas hY) f

/-- An actual affine isomorphism induces the actual point diffeomorphism. -/
def smoothAffinePostcompDiffeomorph
    (hX : SmoothOfRelativeDimension d X.hom)
    (hY : SmoothOfRelativeDimension e Y.hom) (f : X ≅ Y) :
    @Diffeomorph ℝ _ (Fin d → k) _ _ (Fin e → k) _ _
      (Fin d → k) _ (Fin e → k) _
      𝓘(ℝ, Fin d → k) 𝓘(ℝ, Fin e → k)
      (RingPoint k X k) _ (smoothAffineChartedSpace hX)
      (RingPoint k Y k) _ (smoothAffineChartedSpace hY) ∞ :=
  (smoothAffineRegularAtlas hX).postcompDiffeomorph (smoothAffineRegularAtlas hY) f

/-- The point diffeomorphism has the actual postcomposition maps in both directions. -/
theorem smoothAffinePostcompDiffeomorph_maps
    (hX : SmoothOfRelativeDimension d X.hom)
    (hY : SmoothOfRelativeDimension e Y.hom) (f : X ≅ Y) :
    let eF := @Diffeomorph.toEquiv ℝ _ (Fin d → k) _ _ (Fin e → k) _ _
      (Fin d → k) _ (Fin e → k) _
      𝓘(ℝ, Fin d → k) 𝓘(ℝ, Fin e → k)
      (RingPoint k X k) _ (smoothAffineChartedSpace hX)
      (RingPoint k Y k) _ (smoothAffineChartedSpace hY) ∞
      (smoothAffinePostcompDiffeomorph hX hY f)
    (∀ p, eF p = p ≫ f.hom) ∧ (∀ q, eF.symm q = q ≫ f.inv) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- Any valid choice of regular atlas gives the identity diffeomorphism from the
chosen construction, including on empty point spaces and across model dimensions. -/
theorem smoothAffineAtlasIndependence
    (hsmooth : SmoothOfRelativeDimension d X.hom) (e : ℕ) (B : RegularAtlas k X e) :
    ∃ F : @Diffeomorph ℝ _ (Fin d → k) _ _ (Fin e → k) _ _
        (Fin d → k) _ (Fin e → k) _
        𝓘(ℝ, Fin d → k) 𝓘(ℝ, Fin e → k)
        (RingPoint k X k) _ (smoothAffineChartedSpace hsmooth)
        (RingPoint k X k) _ B.chartedSpace ∞,
      let eF := @Diffeomorph.toEquiv ℝ _ (Fin d → k) _ _ (Fin e → k) _ _
        (Fin d → k) _ (Fin e → k) _
        𝓘(ℝ, Fin d → k) 𝓘(ℝ, Fin e → k)
        (RingPoint k X k) _ (smoothAffineChartedSpace hsmooth)
        (RingPoint k X k) _ B.chartedSpace ∞ F
      eF = Equiv.refl (RingPoint k X k) :=
  (smoothAffineRegularAtlas hsmooth).independence B

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type w} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type z} [TopologicalSpace M] [ChartedSpace H M]

/-- The intrinsic family criterion for this particular chosen construction. -/
theorem smoothAffine_contMDiff_iff_regularSmooth
    (hsmooth : SmoothOfRelativeDimension d X.hom) (f : M → RingPoint k X k) :
    letI := smoothAffineChartedSpace hsmooth
    ContMDiff I 𝓘(ℝ, Fin d → k) ∞ f ↔ RegularSmooth I f :=
  (smoothAffineRegularAtlas hsmooth).contMDiff_iff_regularSmooth I f

end Langlands.AlgebraicGeometry.PointManifold.General
