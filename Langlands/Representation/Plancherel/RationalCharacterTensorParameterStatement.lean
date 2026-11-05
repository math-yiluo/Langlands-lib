import Langlands.Representation.Plancherel.RationalCharacterTensorParameter

/-! # Rational-character tensors identify the actual complex image dual -/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

/-- For an actual connected reductive group over any nonarchimedean local
field, complex scalar extension of rational-character evaluation identifies
the rational-character tensor space with the complex dual of the actual
integer valuation image. -/
def RationalCharacterTensorParameterStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    (_hG : GroupScheme.IsConnectedReductive G),
    Function.Bijective (rationalCharacterTensorParameter G)

end Langlands.Plancherel
