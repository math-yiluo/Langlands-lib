import Langlands.LocalField.Canonical
import Langlands.LocalField.RelativeIntegers
import Langlands.ClassFieldTheory.Local.GradedUnitCoordinates
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! Algebraic generation of a totally ramified p-adic integer ring by every
supplied uniformizer. This module states the arithmetic prerequisite. -/

namespace Langlands.LocalClassField

universe u v

/-- Every order-one element generates the actual extension integer ring over
the actual base integer ring in a totally ramified finite extension. -/
def TotallyRamifiedIntegerMonogeneity : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (L : PadicField.{v} p)
    [Algebra F.Carrier L.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]
    [FiniteDimensional F.Carrier L.Carrier],
    let TF := F.canonicalTopologicalData
    let TL := L.canonicalTopologicalData
    letI := PadicField.TopologicalData.relativeIntegerAlgebra TF TL
    TL.ramificationIndex = Module.finrank F.Carrier L.Carrier * TF.ramificationIndex →
      ∀ (π : L.Carrier) (hπ : TL.ord π = 1),
        Algebra.adjoin TF.Integers {TL.coordinateUniformizer π hπ} =
          (⊤ : Subalgebra TF.Integers TL.Integers)

end Langlands.LocalClassField
