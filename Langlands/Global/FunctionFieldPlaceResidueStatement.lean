import Langlands.Global.FunctionFieldValuationPlaces

/-! # Finite residue extensions at actual function-field places -/

universe u

namespace Langlands.Global

/-- The residue fields of actual curve places are finite extensions of the
constant field. No perfectness or separability of the presentation is assumed. -/
def FunctionFieldPlaceResidueStatement : Prop :=
  ∀ (k F : Type u) [Field k] [Field F] [Algebra k F]
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    [FunctionField k F] (v : AlgebraicCurve.Place k F),
      Module.Finite k v.ResidueField

end Langlands.Global
