import Langlands.Algebra.LocalDivisionResidueScalar

/-! The local central division-algebra residue degree formula. -/

namespace Langlands.CentralDivision

open ValuativeRel

universe u

/-- The actual residue extension has degree equal to the canonical reduced degree. -/
def LocalResidueDegreeStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (D : Type u) [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
    [Algebra.IsCentral K D],
    letI := localDivisionResidueField K D
    letI := localDivisionResidueAlgebra K D
    Module.finrank 𝓀[K]
      (DivisionValuation.Residue (localReducedNormValuation K D)) =
        Langlands.CentralSimple.reducedDegree K D

end Langlands.CentralDivision
