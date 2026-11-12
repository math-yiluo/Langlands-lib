import Langlands.AlgebraicGeometry.PointManifold.General.StandardSmoothNeighborhoods
import Langlands.AlgebraicGeometry.PointManifold.Analytic.PrincipalOpenRegularCharts
import Langlands.AlgebraicGeometry.PointManifold.Analytic.RegularCharts

/-! # Analytic Reduction of regular atlas existence to standard-smooth affine charts -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointManifold.Analytic

open PointTopology

variable (k : Type u) [NontriviallyNormedField k] [CompleteSpace k]
variable (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] (d : ℕ)

local instance reductionBasicOpen_isAffine (f : AffineCoordinateRing k X) :
    IsAffine (X.left.basicOpen (U := ⊤) f) :=
  (isAffineOpen_top X.left).basicOpen f

/-- Pointwise regular charts on standard-smooth affine coordinate algebras give
a covering atlas on every algebraically smooth affine scheme. -/
def RegularAtlas.ofStandardSmooth
    (H : ∀ (Y : Over (Spec (CommRingCat.of k))) [IsAffine Y.left],
      Algebra.IsStandardSmoothOfRelativeDimension d k (AffineCoordinateRing k Y) →
      ∀ q : RingPoint k Y k, ∃ C : RegularChart k Y d, q ∈ C.homeomorph.source)
    [SmoothOfRelativeDimension d X.hom] :
    RegularAtlas k X d := by
  classical
  have local_exists (p : RingPoint k X k) :
      ∃ C : RegularChart k X d, p ∈ C.homeomorph.source := by
    let N := General.standardSmoothPrincipalNeighborhood k X d
      (p.left (IsLocalRing.closedPoint k))
    let U := X.left.basicOpen (U := ⊤) N.function
    have hp : Set.range p.left ⊆ U :=
      (range_subset_open_iff_closedPoint k X k U p).mpr N.mem_basicOpen
    let q := openPointLift k X k U p hp
    obtain ⟨C, hC⟩ := H (openOver k X U) N.standardSmooth q
    refine ⟨C.ofBasicOpen N.function, ?_⟩
    rw [RegularChart.ofBasicOpen_source]
    exact ⟨q, hC, openPointMap_lift k X k U p hp⟩
  exact {
    chartAt := fun p => (local_exists p).choose
    mem_source := fun p => (local_exists p).choose_spec }


end Langlands.AlgebraicGeometry.PointManifold.Analytic
