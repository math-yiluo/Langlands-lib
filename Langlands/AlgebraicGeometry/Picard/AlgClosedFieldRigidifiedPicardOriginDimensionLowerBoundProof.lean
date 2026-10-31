import Langlands.AlgebraicGeometry.Picard.PicardOriginMumfordClassifier
import Langlands.AlgebraicGeometry.QuasiFiniteAtStalkDimensionProof
import Langlands.AlgebraicGeometry.FieldSmoothClosedPointStalkDimensionProof

/-! # Proof: the origin local-dimension bound from a finite rational translation stabilizer -/

universe u

namespace Langlands.AbelianScheme

/-- If a line bundle on an abelian variety of relative dimension `g` over an algebraically
closed field has a finite rational translation stabilizer, then the stalk of a locally finite
type universal rigidified Picard parameter at its origin has Krull dimension at least `g`. -/
theorem algClosedFieldRigidifiedPicardOriginDimensionLowerBound :
    AlgClosedFieldRigidifiedPicardOriginDimensionLowerBoundStatement.{u} :=
  algClosedFieldRigidifiedPicardOriginDimensionLowerBound_of_stalkDimension
    Langlands.AlgebraicGeometry.quasiFiniteAtStalkDimension
    Langlands.AlgebraicGeometry.fieldSmoothClosedPointStalkDimension

end Langlands.AbelianScheme
