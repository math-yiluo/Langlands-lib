import Langlands.AbelianScheme.FieldAbelianVarietyPresentationStatement
import Langlands.AbelianScheme.SmoothGeometricIntegralityProof

/-! # Proof of the source presentation of abelian group schemes over fields -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The source presentation follows from geometric integrality of smooth
geometrically connected schemes over fields. -/
theorem fieldAbelianVarietyPresentation_of_smoothGeometricIntegrality
    (hint : Langlands.AbelianScheme.SmoothGeometricIntegrality.{u}) :
    FieldAbelianVarietyPresentationStatement.{u} := by
  intro K _ G _ hsm hpr hgc
  refine ⟨inferInstance, inferInstance, inferInstance, ?_, hint K G.X.left G.X.hom hsm hgc⟩
  obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  exact ⟨η[G.X].left x⟩

/-- A commutative smooth proper geometrically connected group scheme over any
field is of finite type, separated, nonempty and geometrically integral. -/
theorem fieldAbelianVarietyPresentation : FieldAbelianVarietyPresentationStatement.{u} :=
  fieldAbelianVarietyPresentation_of_smoothGeometricIntegrality
    Langlands.AbelianScheme.smoothGeometricIntegrality

end Langlands.GroupScheme
