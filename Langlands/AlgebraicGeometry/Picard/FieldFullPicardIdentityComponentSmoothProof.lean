import Langlands.AlgebraicGeometry.Picard.FieldFullPicardIdentityComponentSmoothStatement
import Langlands.AlgebraicGeometry.Picard.FieldRigidifiedPicardParameterGeometricallyReducedProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalGroupObject
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AlgebraicGeometry.Modules.PullbackTensorUnitProofs
import Langlands.AlgebraicGeometry.Modules.ExplicitPullbackTensorAssociativityProofs
import Langlands.AlgebraicGeometry.Modules.TensorMonoidalComparisonProofs
import Langlands.AlgebraicGeometry.Modules.PullbackTensorCompatibilityProofs
import Langlands.AlgebraicGeometry.Picard.LocalComparisonProof
import Mathlib.AlgebraicGeometry.Group.Smooth

/-! # Smoothness of a supplied full Picard identity-component open over a field -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- Every supplied identity-component open of a locally finite type universal rigidified
Picard parameter over an arbitrary field is smooth as an actual open subscheme. -/
theorem fieldFullPicardIdentityComponentSmooth :
    FieldFullPicardIdentityComponentSmoothStatement.{u} := by
  intro k _ A P L hL hP U _
  let : LocallyOfFiniteType P.hom := hP
  let : GeometricallyReduced P.hom :=
    fieldRigidifiedPicardParameterGeometricallyReduced k A P L hL hP
  let : CommGrpObj P :=
    RigidifiedLineBundle.universalCommGrpObj pullbackTensorComparisonIsIso
      pullbackTensorUnitCoherence explicitPullbackTensorAssociativity
      tensorMonoidalLeftUnitorComparison pullbackTensorSymmetry
      locallyFreeRankOneIffTensorInvertible A.X.hom (unitSection A)
      (unitSection_comp A) pullbackTensorComposition L hL
  let : GrpObj (Over.mk P.hom) := inferInstanceAs (GrpObj P)
  let : Smooth P.hom := smooth_of_grpObj P.hom
  change Smooth (U.ι ≫ P.hom)
  infer_instance

end Langlands.AbelianScheme
