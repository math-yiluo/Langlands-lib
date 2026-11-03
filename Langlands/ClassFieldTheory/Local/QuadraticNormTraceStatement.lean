import Langlands.LocalField.Normalization.Definitions
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Defs

/-! Quadratic norm–trace expansion in the actual supplied p-adic integer rings. -/

namespace Langlands.LocalClassField

universe u v

/-- The field norm of `1 + a*y` agrees with its linear trace term modulo `a² O_F`.
The coefficient `a` and both integer rings are the supplied actual objects. -/
def QuadraticNormTraceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    (T : F.TopologicalData) (S : E.TopologicalData)
    (a : T.Integers) (y : S.Integers),
    ∃ r : T.Integers,
      Algebra.norm F.Carrier
          (1 + algebraMap F.Carrier E.Carrier (a : F.Carrier) * (y : E.Carrier)) =
        1 + (a : F.Carrier) * Algebra.trace F.Carrier E.Carrier (y : E.Carrier) +
          (a : F.Carrier) ^ 2 * (r : F.Carrier)

end Langlands.LocalClassField
