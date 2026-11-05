import Langlands.Global.AdelicUnitLocusStatement
import Langlands.Global.AdelicNonunitSequence

/-! # Proof of the actual adelic unit-locus obstruction -/

noncomputable section

universe u

open CategoryTheory Filter Topology

namespace Langlands.AlgebraicGeometry.PointTopology

/-- A nonunit sequence converging to one obstructs openness of the actual
punctured-affine-line point image. -/
theorem affineLineUnitLocusObstruction_of_nonunit_tendsto
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [TopologicalSpace S] [IsTopologicalRing S]
    (x : ℕ → S) (hx : ∀ n, ¬ IsUnit (x n))
    (ht : Tendsto x atTop (𝓝 1)) :
    AffineLineUnitLocusObstruction R S := by
  have hclosed : ¬ IsClosed {s : S | ¬ IsUnit s} := by
    intro hc
    have h1 : (1 : S) ∈ {s : S | ¬ IsUnit s} :=
      hc.mem_of_tendsto ht (Eventually.of_forall hx)
    exact h1 isUnit_one
  have hopen : ¬ IsOpen {s : S | IsUnit s} := by
    intro ho
    exact hclosed ho.isClosed_compl
  refine ⟨hopen, hclosed, ?_⟩
  intro ho
  apply hopen
  have ho' : IsOpen (X := RingPoint R (ringTest R (MvPolynomial Unit R)) S)
      {p | IsUnit (affineLinePointEquiv R S p)} := by
    rw [← range_affineLinePuncture_points R S]
    exact ho
  have hp := IsOpen.preimage (affineLinePointHomeomorph R S).symm.continuous ho'
  have he : (affineLinePointHomeomorph R S).symm ⁻¹'
      {p | IsUnit (affineLinePointEquiv R S p)} = {s : S | IsUnit s} := by
    ext s
    change IsUnit (affineLinePointHomeomorph R S
      ((affineLinePointHomeomorph R S).symm s)) ↔ IsUnit s
    rw [Homeomorph.apply_symm_apply]
  rwa [he] at hp

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

theorem numberFieldUnitLocus : NumberFieldUnitLocusStatement.{u} := by
  intro K _ _
  exact affineLineUnitLocusObstruction_of_nonunit_tendsto K (Adeles K)
    (numberFieldNonunitSequence K) (numberFieldNonunitSequence_not_isUnit K)
    (tendsto_numberFieldNonunitSequence K)

theorem curvePlaceUnitLocus : CurvePlaceUnitLocusStatement.{u} := by
  intro k F _ _ _ _ _ _ _
  exact affineLineUnitLocusObstruction_of_nonunit_tendsto F (CurvePlaceAdeleRing k F)
    (curvePlaceNonunitSequence k F) (curvePlaceNonunitSequence_not_isUnit k F)
    (tendsto_curvePlaceNonunitSequence k F)

/-- The openness obstruction for actual adelic points in both characteristics. -/
theorem adelicUnitLocus : AdelicUnitLocusStatement.{u} :=
  ⟨numberFieldUnitLocus, curvePlaceUnitLocus⟩

end Langlands.Global
