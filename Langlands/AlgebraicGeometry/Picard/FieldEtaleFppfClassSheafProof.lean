import Langlands.AlgebraicGeometry.Picard.SubschemeRigidifiedComparison
import Langlands.AlgebraicGeometry.Picard.RigidifyingFiniteSubscheme

/-! # The etale Picard class sheaf of a proper scheme over a field is an fppf sheaf -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- For a proper scheme over an arbitrary field, the etale sheafification of the relative
line-bundle classes is an fppf sheaf on the entire scheme slice. -/
theorem fieldEtaleFppfClassSheaf : FieldEtaleFppfClassSheafStatement.{u} := by
  intro k _ X hX
  obtain ⟨Z, z, hfin, hinj⟩ := RigidifyingSubscheme.exists_finite_injective X.hom
  exact SubschemeRigidification.isSheaf_etaleClassSheafPresheaf_of_rigidifying X.hom
    (z ≫ X.hom) z rfl (RigidifyingSubscheme.injective_zRel_appTop X.hom (z ≫ X.hom) z rfl hinj)

end Langlands.AlgebraicGeometry.Picard
