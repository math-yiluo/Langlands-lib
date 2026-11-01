import Langlands.AlgebraicGeometry.Picard.LineBundle
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.QuasiAffine

/-! # Realizing a line bundle as an invertible ideal on a quasi-affine scheme -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Every line bundle on a Noetherian quasi-affine scheme admits a monomorphism
into its structure module. This is a statement, not a chosen embedding or a proof. -/
def QuasiAffineLineBundleIdealEmbeddingStatement : Prop :=
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [Scheme.IsQuasiAffine X]
    (D : LineBundle X),
    ∃ s : D.obj ⟶ SheafOfModules.unit X.ringCatSheaf, Mono s

end Langlands.AlgebraicGeometry.Picard
