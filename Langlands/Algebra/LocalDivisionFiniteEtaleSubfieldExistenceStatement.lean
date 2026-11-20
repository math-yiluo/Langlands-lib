import Langlands.Algebra.LocalDivisionFullResidueSubfieldEtaleStatement
import Langlands.Algebra.LocalDivisionReducedDegree

/-! An actual full-residue subfield of reduced degree with finite étale integer ring. -/

namespace Langlands.CentralDivision

open ValuativeRel

universe u

/-- The original singleton adjoin of an integral element can give a full-residue field of
reduced degree whose actual integer algebra is finite étale. -/
def LocalDivisionFiniteEtaleSubfieldExistenceStatement : Prop :=
  ∀ (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
    [FiniteDimensional K D] [Algebra.IsCentral K D],
    ∃ b : (localReducedNormValuation K D).integer,
      let E := residueGeneratorSubalgebra K D (b : D)
      letI : Field E := residueGeneratorField K D (b : D)
      let ι := E.val
      letI := localDivisionSubfieldIntegerAlgebra K D ι
      Function.Surjective (localDivisionSubfieldResidueMap K D ι) ∧
        FiniteDimensional K E ∧
        Module.Finite 𝒪[K] (localDivisionSubfieldValuation K D ι).integer ∧
        Algebra.Etale 𝒪[K] (localDivisionSubfieldValuation K D ι).integer ∧
        Module.finrank K E = CentralSimple.reducedDegree K D

/-- The integral étaleness criterion supplies the remaining property of the original
full-residue witness of reduced degree. -/
theorem localDivisionFiniteEtaleSubfieldExistence_of_fullResidueEtale
    (hEtale : LocalDivisionFullResidueSubfieldEtaleStatement.{u, u}) :
    LocalDivisionFiniteEtaleSubfieldExistenceStatement.{u} := by
  intro K D _ _ _ _ _ _ _ _
  obtain ⟨b, _, hsurj, hdegree, _, _⟩ :=
    exists_localDivision_fullResidue_reducedDegree_cyclic_subfield K D
  let := residueGeneratorField K D (b : D)
  let ι := (residueGeneratorSubalgebra K D (b : D)).val
  exact ⟨b, hsurj, inferInstance, localDivisionSubfieldInteger_finite K D ι,
    hEtale K D ι hsurj hdegree, hdegree⟩

end Langlands.CentralDivision
