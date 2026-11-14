import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Injectivity of `H₁(L_{L/K}) ⊗_L M → H₁(L_{M/K})` for towers of fields -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks More on Algebra, Lemma 15.35.2 (07E2), first map of the six-term exact sequence: for
field extensions `M/L/K`, the map `H₁(L_{L/K}) ⊗_L M → H₁(L_{M/K})` is injective. -/
def FieldH1CotangentInjectiveStatement : Prop :=
  ∀ (K L M : Type u) [Field K] [Field L] [Field M] [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M],
    Function.Injective ((Algebra.H1Cotangent.map K K L M).liftBaseChange M)

end Langlands.CommutativeAlgebra.Popescu
