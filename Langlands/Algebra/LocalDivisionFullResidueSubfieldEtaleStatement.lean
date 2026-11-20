import Langlands.Algebra.LocalDivisionSubfieldInteger
import Mathlib.RingTheory.Etale.Basic

/-! Étaleness of the actual integer algebra of a full-residue subfield of reduced degree. -/

namespace Langlands.CentralDivision

open ValuativeRel

universe u uL

/-- Full actual residue and the reduced degree force the original integer algebra to be étale. -/
def LocalDivisionFullResidueSubfieldEtaleStatement : Prop :=
  ∀ (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
    [FiniteDimensional K D] [Algebra.IsCentral K D]
    {L : Type uL} [Field L] [Algebra K L] [FiniteDimensional K L] (ι : L →ₐ[K] D),
    Function.Surjective (localDivisionSubfieldResidueMap K D ι) →
    Module.finrank K L = CentralSimple.reducedDegree K D →
    letI := localDivisionSubfieldIntegerAlgebra K D ι
    Algebra.Etale 𝒪[K] (localDivisionSubfieldValuation K D ι).integer

end Langlands.CentralDivision
