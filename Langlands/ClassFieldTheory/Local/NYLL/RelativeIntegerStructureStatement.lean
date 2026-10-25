import Langlands.LocalField.RelativeIntegers

/-! Relative integral closure and finiteness for supplied p-adic integer rings. -/

namespace Langlands.LocalClassField.NYLL

universe u v

/-- The supplied extension integer ring is the integral closure of the supplied
base integer ring and is finite over it for the named relative scalars. -/
def RelativeIntegerStructureStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    (T : F.TopologicalData) (S : E.TopologicalData),
    letI := PadicField.TopologicalData.relativeIntegerAlgebra T S
    letI := PadicField.TopologicalData.relativeIntegerFieldAlgebra (E := E) T
    IsIntegralClosure S.Integers T.Integers E.Carrier ∧
      Module.Finite T.Integers S.Integers

end Langlands.LocalClassField.NYLL
