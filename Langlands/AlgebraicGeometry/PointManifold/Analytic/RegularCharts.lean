import Langlands.AlgebraicGeometry.PointManifold.Analytic.RegularEvaluation

/-! # Analytic regular charts on the existing affine point topology -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped Manifold ContDiff

namespace Langlands.AlgebraicGeometry.PointManifold.Analytic

open PointTopology

variable (k : Type u) [NontriviallyNormedField k] [CompleteSpace k]
variable (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left] (d : ℕ)

/-- Local analytic output, to be constructed from algebraic smoothness.
The chart is a partial homeomorphism for the already published evaluation topology. -/
structure RegularChart where
  homeomorph : OpenPartialHomeomorph (RingPoint k X k) (Fin d → k)
  numerator : Fin d → AffineCoordinateRing k X
  denominator : Fin d → AffineCoordinateRing k X
  denominator_ne_zero : ∀ p ∈ homeomorph.source, ∀ i,
    regularEvaluation p (denominator i) ≠ 0
  apply_eq : ∀ p ∈ homeomorph.source, ∀ i,
    homeomorph p i =
      regularEvaluation p (numerator i) / regularEvaluation p (denominator i)
  contDiffOn_inverse_evaluation : ∀ a : AffineCoordinateRing k X,
    ContDiffOn k ω (fun v => regularEvaluation (homeomorph.symm v) a) homeomorph.target

/-- A covering family of regular charts, without an algebraic smoothness assumption. -/
structure RegularAtlas where
  chartAt : RingPoint k X k → RegularChart k X d
  mem_source : ∀ p, p ∈ (chartAt p).homeomorph.source

namespace RegularAtlas

variable {k X d}

/-- The charted space uses the existing actual point carrier and evaluation topology. -/
@[instance_reducible] def chartedSpace (A : RegularAtlas k X d) :
    ChartedSpace (Fin d → k) (RingPoint k X k) where
  atlas := Set.range (fun p => (A.chartAt p).homeomorph)
  chartAt p := (A.chartAt p).homeomorph
  mem_chart_source := A.mem_source
  chart_mem_atlas p := ⟨p, rfl⟩

/-- Empty point spaces have a covering regular atlas, in every dimension. -/
def ofIsEmpty [IsEmpty (RingPoint k X k)] : RegularAtlas k X d where
  chartAt p := isEmptyElim p
  mem_source p := isEmptyElim p

end RegularAtlas


end Langlands.AlgebraicGeometry.PointManifold.Analytic
