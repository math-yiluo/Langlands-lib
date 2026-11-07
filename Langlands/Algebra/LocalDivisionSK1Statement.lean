import Langlands.Algebra.ReducedNorm
import Mathlib.RingTheory.SimpleRing.DivisionRing
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.NumberTheory.LocalField.Basic

/-! Triviality of the reduced Whitehead group of a local central division algebra. -/

namespace Langlands.CentralDivision

universe u

/-- Over a nonarchimedean local field, the kernel of the actual reduced norm
on the original division-algebra units is precisely their commutator subgroup. -/
def LocalSK1Statement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (D : Type u) [DivisionRing D] [Algebra F D] [FiniteDimensional F D]
    [Algebra.IsCentral F D],
    ((Langlands.CentralSimple.reducedNormUnits F D F).comp
      (Units.map Algebra.TensorProduct.includeRight.toMonoidHom)).ker =
        commutator Dˣ

end Langlands.CentralDivision
