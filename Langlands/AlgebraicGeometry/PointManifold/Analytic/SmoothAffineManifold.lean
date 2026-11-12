import Langlands.AlgebraicGeometry.PointManifold.Analytic.StandardSmoothReduction
import Langlands.AlgebraicGeometry.PointManifold.Analytic.StandardSmoothRegularCharts
import Langlands.AlgebraicGeometry.PointManifold.Analytic.RegularAtlasFunctoriality

/-! # Analytic manifolds of actual smooth affine points over complete fields -/

noncomputable section
universe u
open CategoryTheory
open _root_.AlgebraicGeometry
open scoped ContDiff Manifold
namespace Langlands.AlgebraicGeometry.PointManifold.Analytic
open PointTopology
variable (k : Type u) [NontriviallyNormedField k] [CompleteSpace k]
variable (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] (d : ℕ)

/-- Algebraic smoothness of constant relative dimension supplies an analytic regular atlas. -/
def smoothAffineRegularAtlas (h : SmoothOfRelativeDimension d X.hom) : RegularAtlas k X d := by
  letI := h
  exact RegularAtlas.ofStandardSmooth k X d
    (fun Y _ hY p => exists_regularChart_of_standardSmooth hY p)

/-- The analytic charts retain the existing topology on actual relative points. -/
@[instance_reducible] def smoothAffineChartedSpace (h : SmoothOfRelativeDimension d X.hom) :
    ChartedSpace (Fin d → k) (RingPoint k X k) :=
  (smoothAffineRegularAtlas k X d h).chartedSpace

/-- The resulting affine manifold is analytic over the original coefficient field. -/
theorem smoothAffineIsManifold (h : SmoothOfRelativeDimension d X.hom) :
    letI := smoothAffineChartedSpace k X d h
    IsManifold 𝓘(k, Fin d → k) ω (RingPoint k X k) :=
  (smoothAffineRegularAtlas k X d h).isManifold

/-- Every global regular function is analytic on the constructed manifold. -/
theorem smoothAffine_contMDiff_regularEvaluation (h : SmoothOfRelativeDimension d X.hom)
    (a : AffineCoordinateRing k X) :
    letI := smoothAffineChartedSpace k X d h
    ContMDiff 𝓘(k, Fin d → k) 𝓘(k, k) ω
      (fun p : RingPoint k X k => regularEvaluation p a) :=
  (smoothAffineRegularAtlas k X d h).contMDiff_regularEvaluation a

/-- Every actual affine scheme morphism is analytic between the constructed manifolds. -/
theorem smoothAffine_contMDiff_postcomp
    {Y : Over (Spec (CommRingCat.of k))} [IsAffine Y.left] {e : ℕ}
    (hX : SmoothOfRelativeDimension d X.hom) (hY : SmoothOfRelativeDimension e Y.hom)
    (f : X ⟶ Y) :
    @ContMDiff k _ (Fin d → k) _ _ (Fin d → k) _ 𝓘(k, Fin d → k)
      (RingPoint k X k) _ (smoothAffineChartedSpace k X d hX)
      (Fin e → k) _ _ (Fin e → k) _ 𝓘(k, Fin e → k)
      (RingPoint k Y k) _ (smoothAffineChartedSpace k Y e hY) ω (fun p => p ≫ f) :=
  (smoothAffineRegularAtlas k X d hX).contMDiff_postcomp
    (smoothAffineRegularAtlas k Y e hY) f

end Langlands.AlgebraicGeometry.PointManifold.Analytic
