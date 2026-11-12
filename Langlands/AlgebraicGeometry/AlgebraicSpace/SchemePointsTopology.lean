import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemePointsComparison
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation

/-! # Topological comparison of represented presheaf points -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Topology

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The defining test for an open subset of presheaf points. -/
theorem isOpen_pointTopology_iff (F : Presheaf S) (O : Set (Points F)) :
    IsOpen[pointTopology F] O ↔
      ∀ (U : Over S) (a : (schemeYoneda S).obj U ⟶ F), IsEtale a →
        IsOpen ((Points.map a ∘ schemePoint U) ⁻¹' O) := by
  simp only [isOpen_iSup_iff, isOpen_coinduced]

/-- A map out of the point space is continuous exactly when its restrictions
along all étale scheme charts are continuous. -/
theorem continuous_pointTopology_iff (F : Presheaf S)
    {A : Type v} [TopologicalSpace A] (f : Points F → A) :
    Continuous[pointTopology F, _] f ↔
      ∀ (U : Over S) (a : (schemeYoneda S).obj U ⟶ F), IsEtale a →
        Continuous (f ∘ Points.map a ∘ schemePoint U) := by
  simp only [continuous_iSup_dom, continuous_coinduced_dom]

/-- Every étale chart in the definition of the point topology is continuous. -/
theorem continuous_schemePoint_chart {F : Presheaf S} {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ F) (ha : IsEtale a) :
    Continuous[_, pointTopology F] (Points.map a ∘ schemePoint U) := by
  rw [continuous_iff_coinduced_le]
  exact le_iSup_of_le U (le_iSup_of_le a (le_iSup_of_le ha le_rfl))

/-- The comparison from represented presheaf points to the scheme is continuous. -/
theorem continuous_schemePointsTo (U : Over S) :
    Continuous[pointTopology ((schemeYoneda S).obj U), _] (schemePointsTo U) := by
  rw [continuous_pointTopology_iff]
  intro V a _
  obtain ⟨g, rfl⟩ := (schemeYoneda S).map_surjective a
  have heq : (schemePointsTo U ∘ Points.map ((schemeYoneda S).map g) ∘ schemePoint V) =
      g.left := by
    funext x
    simp only [Function.comp_apply, schemePointsTo_map, schemePointsTo_schemePoint]
  rw [heq]
  exact g.left.continuous

/-- The canonical residue-field point map from a scheme is continuous. -/
theorem continuous_schemePoint (U : Over S) :
    Continuous[_, pointTopology ((schemeYoneda S).obj U)] (schemePoint U) := by
  have hid : IsEtale (𝟙 ((schemeYoneda S).obj U)) := by
    rw [← (schemeYoneda S).map_id U]
    exact isEtale_map (𝟙 U) (by infer_instance)
  have h := continuous_schemePoint_chart (𝟙 ((schemeYoneda S).obj U)) hid
  have heq : (Points.map (𝟙 ((schemeYoneda S).obj U)) ∘ schemePoint U) = schemePoint U := by
    funext x
    exact Points.map_id _
  rwa [heq] at h

/-- The quotient of field-valued points of a represented presheaf, with its
étale-chart topology, is homeomorphic to the actual representing scheme. -/
def schemePointsHomeomorph (U : Over S) :
    letI := pointTopology ((schemeYoneda S).obj U)
    Points ((schemeYoneda S).obj U) ≃ₜ U.left := by
  letI := pointTopology ((schemeYoneda S).obj U)
  exact
    { toEquiv := schemePointsEquiv U
      continuous_toFun := continuous_schemePointsTo U
      continuous_invFun := continuous_schemePoint U }

end Langlands.AlgebraicGeometry.AlgebraicSpace
