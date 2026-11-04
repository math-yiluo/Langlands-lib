import Langlands.GroupScheme.MatrixRepresentation.SmoothNormalKernel

/-! # Affineness of a represented fpqc quotient of an affine algebraic group -/

universe u

namespace Langlands.GroupScheme

/-- A flat, surjective, quasi-compact quotient homomorphism of an affine
algebraic group over any field has affine represented target. -/
theorem affineGroupSchemeQuotient : AffineGroupSchemeQuotientStatement.{u} :=
  AffineQuotient.affineGroupSchemeQuotient_of_smoothNormalKernel
    AffineQuotient.smoothNormalKernel

end Langlands.GroupScheme
