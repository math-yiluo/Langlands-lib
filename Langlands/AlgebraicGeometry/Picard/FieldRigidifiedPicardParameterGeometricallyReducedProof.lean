import Langlands.AlgebraicGeometry.Picard.FieldRigidifiedPicardParameterGeometricallyReducedStatement
import Langlands.AlgebraicGeometry.Picard.AlgClosedFieldRigidifiedPicardParameterReducedProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalBaseChangeProof
import Langlands.AlgebraicGeometry.GeometricallyReducedOfAlgClosedProof

/-! # Geometric reducedness of an actual universal rigidified Picard parameter -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- A locally finite type parameter carrying an actual universal rigidified family
for an abelian scheme over any field is geometrically reduced. -/
theorem fieldRigidifiedPicardParameterGeometricallyReduced :
    FieldRigidifiedPicardParameterGeometricallyReducedStatement.{u} := by
  intro k _ A P L hL hFiniteType
  let : LocallyOfFiniteType P.hom := hFiniteType
  apply Langlands.AlgebraicGeometry.geometricallyReducedOfAlgClosed P.left _ P.hom
  intro K _ _ b
  exact algClosedFieldRigidifiedPicardParameterReduced
    K ((baseChange b).obj A) ((Over.pullback b).obj P)
    ((baseChangeFamily b A P).obj L)
    (rigidifiedUniversalBaseChange _ _ b A P L hL) (by
      change LocallyOfFiniteType (Limits.pullback.snd P.hom b)
      infer_instance)

end Langlands.AbelianScheme
