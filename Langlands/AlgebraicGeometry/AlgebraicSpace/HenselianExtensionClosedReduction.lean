import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianExtensionCompletionReduction
import Langlands.AlgebraicGeometry.AlgebraicSpace.CompleteExtensionPointClosedRangeStatement

/-! # Reduction of henselian extension closedness to complete fields -/
noncomputable section
universe u
open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (IsHenselianValuedField completionNontriviallyNormedField)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace
namespace ExtensionClosedReduction

/-- Extension of points along the top field of a tower, with the iterated base
change identified with base change from the original field. -/
def towerExtensionPointMap (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    (X : AlgebraicSpace (Spec (CommRingCat.of K))) :
    RingPoints L (baseChange (Spec.algebraMap K L) X) L →
      RingPoints M (baseChange (Spec.algebraMap K M) X) M :=
  RingPoints.map (towerIso K L M X).hom ∘
    fieldExtensionPointMap L M (baseChange (Spec.algebraMap K L) X)

/-- On points of the original space, the tower map is coefficient change. -/
theorem towerExtensionPointMap_eval
    (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    (X : AlgebraicSpace (Spec (CommRingCat.of K)))
    (z : RingPoints L (baseChange (Spec.algebraMap K L) X) L) :
    baseChangeRingPointsEquiv K M M X (towerExtensionPointMap K L M X z) =
      RingPoints.changeRing ((Algebra.ofId L M).restrictScalars K)
        (baseChangeRingPointsEquiv K L L X z) := by
  rw [towerExtensionPointMap, Function.comp_apply, baseChangeRingPointsEquiv_towerIso]
  simp only [fieldExtensionPointMap, Equiv.apply_symm_apply]
  rw [baseChangeRingPointsEquiv_changeRing]

/-- Tower extension is continuous for the actual chart topologies. -/
theorem continuous_towerExtensionPointMap
    (K L M : Type u) [NontriviallyNormedField K] [NontriviallyNormedField L]
    [NontriviallyNormedField M] [NormedAlgebra K L] [NormedAlgebra L M]
    [NormedAlgebra K M] [IsScalarTower K L M]
    (X : AlgebraicSpace (Spec (CommRingCat.of K))) :
    @Continuous _ _ (etaleChartTopology L (baseChange (Spec.algebraMap K L) X))
      (etaleChartTopology M (baseChange (Spec.algebraMap K M) X))
      (towerExtensionPointMap K L M X) := by
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap K L) X) L) :=
    etaleChartTopology L _
  let : TopologicalSpace (RingPoints M
      (baseChange (Spec.algebraMap L M) (baseChange (Spec.algebraMap K L) X)) M) :=
    etaleChartTopology M _
  let : TopologicalSpace (RingPoints M (baseChange (Spec.algebraMap K M) X) M) :=
    etaleChartTopology M _
  exact (isHomeomorph_ringPointsMap_of_iso (towerIso K L M X)).continuous.comp
    (continuous_fieldExtensionPointMap L M _)

/-- Complete-field closedness implies closedness over a henselian extension in
which the original base is closed, for separated spaces. -/
theorem isClosed_range_of_complete
    (hcomplete : CompleteExtensionPointClosedRangeStatement.{u})
    {K L : Type u} [NontriviallyNormedField K] [NontriviallyNormedField L]
    [NormedAlgebra K L] (hL : IsHenselianValuedField L)
    (hclosed : IsClosed (Set.range (algebraMap K L)))
    {X : AlgebraicSpace (Spec (CommRingCat.of K))}
    (hX : IsQuasiSeparatedLocallyFiniteType K X) (hs : IsSeparated X) :
    IsClosed[etaleChartTopology L (baseChange (Spec.algebraMap K L) X)]
      (Set.range (extensionPointMap L X)) := by
  let Kc := UniformSpace.Completion K
  let Lc := UniformSpace.Completion L
  let := completionNontriviallyNormedField K
  let := completionNontriviallyNormedField L
  let := PointTopology.FiniteExtensionCompletion.algebra K L
  let := PointTopology.FiniteExtensionCompletion.normedAlgebra K L
  let XKc := baseChange (Spec.algebraMap K Kc) X
  let XL := baseChange (Spec.algebraMap K L) X
  let XLc := baseChange (Spec.algebraMap K Lc) X
  let Y := baseChange (Spec.algebraMap Kc Lc) XKc
  let : TopologicalSpace (RingPoints L XL L) := etaleChartTopology L XL
  let : TopologicalSpace (RingPoints Lc XLc Lc) := etaleChartTopology Lc XLc
  let : TopologicalSpace (RingPoints Lc Y Lc) := etaleChartTopology Lc Y
  let g := towerExtensionPointMap K L Lc X
  let q := towerExtensionPointMap K Kc Lc X
  have hXKc : IsQuasiSeparatedLocallyFiniteType Kc XKc :=
    ⟨hX.1.baseChange, hX.2.baseChange⟩
  have hq : IsClosed (Set.range q) := by
    have hc := hcomplete Kc Lc XKc hXKc hs.baseChange
    have he := isHomeomorph_ringPointsMap_of_iso (towerIso K Kc Lc X)
    change IsClosed (Set.range (RingPoints.map (towerIso K Kc Lc X).hom ∘
      fieldExtensionPointMap Kc Lc XKc))
    rw [Set.range_comp]
    exact he.isClosedMap _ hc
  have hpre : g ⁻¹' Set.range q = Set.range (extensionPointMap L X) := by
    ext z
    constructor
    · rintro ⟨x, hx⟩
      have h := congrArg (baseChangeRingPointsEquiv K Lc Lc X) hx
      change baseChangeRingPointsEquiv K Lc Lc X (q x) =
        baseChangeRingPointsEquiv K Lc Lc X (g z) at h
      rw [towerExtensionPointMap_eval, towerExtensionPointMap_eval] at h
      change RingPoints.changeRing (ExtensionCompletionReduction.completedBaseAlgHom K L)
          (baseChangeRingPointsEquiv K Kc Kc X x) =
        RingPoints.changeRing (PointTopology.FiniteExtensionCompletion.coeAlgHom K L)
          (baseChangeRingPointsEquiv K L L X z) at h
      obtain ⟨y, hy⟩ := ExtensionCompletionReduction.exists_point_of_completion_eq
        hL hclosed hs _ _ h
      refine ⟨y, (baseChangeRingPointsEquiv K L L X).injective ?_⟩
      rw [extensionPointMap, Equiv.apply_symm_apply]
      exact hy
    · rintro ⟨y, rfl⟩
      refine ⟨extensionPointMap Kc X y, ?_⟩
      exact (fieldExtensionPointMap_tower K Kc Lc X y).trans
        (fieldExtensionPointMap_tower K L Lc X y).symm
  rw [← hpre]
  exact hq.preimage (continuous_towerExtensionPointMap K L Lc X)

/-- The complete-field closed-range core supplies the unchanged full henselian
extension point embedding statement, including its conditional closed embedding. -/
theorem henselianExtensionPointEmbedding_of_complete
    (hcomplete : CompleteExtensionPointClosedRangeStatement.{u}) :
    HenselianExtensionPointEmbeddingStatement.{u} := by
  intro K L _ _ _ hK hL X hX hcov
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  let : TopologicalSpace (RingPoints L (baseChange (Spec.algebraMap K L) X) L) :=
    etaleChartTopology L _
  have he := ExtensionLocalReduction.isEmbedding_of_covered hK hL hX hcov
  refine ⟨he, fun hc => ⟨he, ?_⟩⟩
  exact ExtensionLocalReduction.isClosed_range_of_separated_open hL hX hcov
    (fun U j hj hs => isClosed_range_of_complete hcomplete hL hc
      (ExtensionLocalReduction.separated_open_properties hX j hj hs) hs)

end ExtensionClosedReduction
end Langlands.AlgebraicGeometry.AlgebraicSpace
