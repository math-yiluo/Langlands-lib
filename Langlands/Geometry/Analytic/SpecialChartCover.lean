import Langlands.Geometry.Analytic.FiniteChartGluingAlgebra
import Langlands.Geometry.Analytic.GeneralizedAffinoid.AffinoidCompletedTensor
import Langlands.Geometry.Analytic.AdmissibleEpimorphism

/-! # Actual special finite chart coverings and original-chart examples -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

namespace FiniteChartGluingData

variable {a} (d : FiniteChartGluingData a)

/-- The actual completed-tensor map to the represented overlap is
constructed by extending the two original bounded restrictions. -/
def overlapTensorMap (i j : Fin d.size) :
    BoundedAlgHom K
      (CompletedTensorAlgebra.Algebra K (a.algebra (d.index i)) (a.algebra (d.index j)))
      (a.algebra (d.overlap i j)) :=
  CompletedTensorAlgebra.lift (d.leftRestriction i j) (d.rightRestriction i j)

@[simp]
theorem overlapTensorMap_comp_leftMap (i j : Fin d.size) :
    (d.overlapTensorMap i j).comp
        (CompletedTensorAlgebra.leftMap K (a.algebra (d.index i)) (a.algebra (d.index j))) =
      d.leftRestriction i j :=
  CompletedTensorAlgebra.lift_comp_leftMap _ _

@[simp]
theorem overlapTensorMap_comp_rightMap (i j : Fin d.size) :
    (d.overlapTensorMap i j).comp
        (CompletedTensorAlgebra.rightMap K (a.algebra (d.index i)) (a.algebra (d.index j))) =
      d.rightRestriction i j :=
  CompletedTensorAlgebra.lift_comp_rightMap _ _

/-- The same overlap map in the actual finite affinoid presentation. -/
def overlapPresentationMap (i j : Fin d.size) :
    BoundedAlgHom K
      (AffinoidCoproduct.algebra K (a.algebra (d.index i)) (a.algebra (d.index j)))
      (a.algebra (d.overlap i j)) :=
  AffinoidCoproduct.lift K (a.algebra (d.overlap i j))
    (a.algebra (d.index i)) (a.algebra (d.index j))
    (d.leftRestriction i j) (d.rightRestriction i j)

/-- The explicit finite-presentation map is exactly the genuine
completed-tensor overlap map after the actual bounded comparison. -/
theorem overlapPresentationMap_comp_fromCompletedTensor (i j : Fin d.size) :
    (d.overlapPresentationMap i j).comp
        (AffinoidCoproduct.fromCompletedTensor K
          (a.algebra (d.index i)) (a.algebra (d.index j))) =
      d.overlapTensorMap i j :=
  AffinoidCoproduct.lift_comp_fromCompletedTensor K
    (a.algebra (d.index i)) (a.algebra (d.index j))
    (d.leftRestriction i j) (d.rightRestriction i j)

/-- The source special-cover condition: the compact literal union is
Hausdorff and every genuine completed-tensor overlap map is admissible. -/
def IsSpecialCover : Prop :=
  T2Space d.locus ∧ ∀ i j : Fin d.size, (d.overlapTensorMap i j).IsAdmissibleEpi

/-- The required represented overlaps are input to the finite gluing data;
specialness adds the actual compact Hausdorff and admissibility conditions. -/
theorem isCompact_of_isSpecialCover (_h : d.IsSpecialCover) : IsCompact d.locus :=
  d.isCompact_locus

variable (a)

/-- A single unchanged original chart is an actual finite gluing family. -/
def singleton (parent : a.Index) : FiniteChartGluingData a where
  size := 1
  index _ := parent
  overlap _ _ := parent
  overlap_range _ _ := (Set.inter_self _).symm

@[simp]
theorem locus_singleton (parent : a.Index) :
    (singleton a parent).locus = Set.range (a.chart parent) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact hi
  · intro hx
    exact Set.mem_iUnion.mpr ⟨(0 : Fin 1), hx⟩

/-- The singleton union has the actual original chart spectrum topology,
so Hausdorffness does not require a separated ambient space. -/
theorem t2Space_locus_singleton (parent : a.Index) :
    T2Space (singleton a parent).locus := by
  let : T2Space (Set.range (a.chart parent)) :=
    (a.isEmbedding_chart parent).toHomeomorph.t2Space
  exact (Homeomorph.setCongr (locus_singleton a parent)).symm.t2Space

/-- Every original chart is special: its genuine tensor diagonal has an
actual bounded section from the first completed-tensor leg. -/
theorem isSpecialCover_singleton (parent : a.Index) :
    (singleton a parent).IsSpecialCover := by
  refine ⟨t2Space_locus_singleton a parent, fun i j => ?_⟩
  let d := singleton a parent
  have hl : d.leftRestriction i j = BoundedAlgHom.id K (a.algebra parent) :=
    a.restriction_id parent _
  apply (d.overlapTensorMap i j).isAdmissibleEpi_of_bounded_section
    (CompletedTensorAlgebra.leftMap K (a.algebra parent) (a.algebra parent))
  exact (d.overlapTensorMap_comp_leftMap i j).trans hl

end FiniteChartGluingData

/-- A literal subset is special if it has a finite original-chart cover
with represented overlaps and admissible genuine tensor overlap maps. -/
def IsSpecialSet (W : Set X) : Prop :=
  ∃ d : FiniteChartGluingData a, d.locus = W ∧ d.IsSpecialCover

/-- Original chart ranges satisfy the source special-subset definition,
with the actual singleton family and diagonal map constructed above. -/
theorem isSpecialSet_chart_range (parent : a.Index) :
    a.IsSpecialSet (Set.range (a.chart parent)) :=
  ⟨FiniteChartGluingData.singleton a parent,
    FiniteChartGluingData.locus_singleton a parent,
    FiniteChartGluingData.isSpecialCover_singleton a parent⟩

/-- Compactness of a special set is proved from its actual finite chart cover. -/
theorem IsSpecialSet.isCompact {W : Set X} (h : a.IsSpecialSet W) : IsCompact W := by
  obtain ⟨d, hd, _⟩ := h
  exact hd ▸ d.isCompact_locus

/-- The Hausdorff condition is on the actual special subspace. -/
theorem IsSpecialSet.t2Space {W : Set X} (h : a.IsSpecialSet W) : T2Space W := by
  obtain ⟨d, hd, hspecial⟩ := h
  let : T2Space d.locus := hspecial.1
  exact (Homeomorph.setCongr hd).t2Space

end Langlands.Analytic.IndexedAffinoidAtlas
