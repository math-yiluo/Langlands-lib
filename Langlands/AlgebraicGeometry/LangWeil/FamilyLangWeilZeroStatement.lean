import Langlands.AlgebraicGeometry.LangWeil.FamilyLangWeilStatement

/-!
# The uniform Lang–Weil estimate for families with zero-dimensional fibres

The case `d = 0` of `FamilyLangWeilInDimension`: when every fibre is geometrically irreducible
of dimension `0`, every `κ`-point of the base has exactly one `κ`-point above it.
-/

universe u

namespace Langlands.AlgebraicGeometry.LangWeil

/-- The uniform Lang–Weil estimate in fibre dimension `0`: `FamilyLangWeilInDimension 0`. -/
def FamilyLangWeilZeroStatement : Prop :=
  FamilyLangWeilInDimension.{u} 0

end Langlands.AlgebraicGeometry.LangWeil
