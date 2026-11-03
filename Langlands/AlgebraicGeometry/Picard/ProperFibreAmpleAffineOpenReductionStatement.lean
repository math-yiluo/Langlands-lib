import Langlands.AlgebraicGeometry.Picard.ProperFibreAmpleSpreadingStatement

/-! # Reduction of the proper-family affine-neighbourhood statement -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- Spreading the specified fibre-ample bundle suffices for the proper-family
finite-set affine-neighbourhood statement. This is a statement target. -/
def ProperFibreAmpleAffineOpenReductionStatement : Prop :=
  ProperFibreAmpleSpreadingStatement.{u} →
    ProperFibreAmpleAffineOpenStatement.{u}

end Langlands.AlgebraicGeometry.Picard
