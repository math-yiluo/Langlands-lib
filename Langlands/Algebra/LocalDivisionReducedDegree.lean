import Langlands.Algebra.LocalDivisionDegree
import Langlands.Algebra.DivisionReducedCharpoly
import Langlands.Algebra.LocalDivisionSubfieldCyclic

/-! Original cyclic full-residue subfields of exactly the reduced degree. -/

noncomputable section

namespace Langlands.CentralDivision

open ValuativeRel

universe u

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

local instance reducedDegreeResidueField :
    Field (DivisionValuation.Residue (localReducedNormValuation K D)) :=
  localDivisionResidueField K D
local instance reducedDegreeResidueAlgebra :
    Algebra 𝓀[K] (DivisionValuation.Residue (localReducedNormValuation K D)) :=
  localDivisionResidueAlgebra K D

/-- The actual residue extension has exactly the reduced degree. -/
theorem localDivisionResidue_finrank_eq_reducedDegree :
    Module.finrank 𝓀[K] (DivisionValuation.Residue (localReducedNormValuation K D)) =
      CentralSimple.reducedDegree K D := by
  apply le_antisymm (localDivisionResidue_finrank_le_reducedDegree K D)
  obtain ⟨b, _, hsurj, hdim⟩ := exists_localDivision_fullResidue_degree_subfield K D
  let := residueGeneratorField K D (b : D)
  rw [← hdim]
  exact reducedDegree_le_localDivisionSubfield_finrank K D
    (residueGeneratorSubalgebra K D (b : D)).val hsurj

/-- The original cyclic full-residue subfield has exactly the reduced degree. -/
theorem exists_localDivision_fullResidue_reducedDegree_cyclic_subfield :
    ∃ b : (localReducedNormValuation K D).integer,
      letI := residueGeneratorField K D (b : D)
      IsSeparable K (b : D) ∧
        Function.Surjective (localDivisionSubfieldResidueMap K D
          (residueGeneratorSubalgebra K D (b : D)).val) ∧
        Module.finrank K (residueGeneratorSubalgebra K D (b : D)) =
          CentralSimple.reducedDegree K D ∧
        IsGalois K (residueGeneratorSubalgebra K D (b : D)) ∧
        IsCyclic (residueGeneratorSubalgebra K D (b : D) ≃ₐ[K]
          residueGeneratorSubalgebra K D (b : D)) := by
  obtain ⟨b, hsep, hsurj, hdim, hgal, hcyc⟩ :=
    exists_localDivision_fullResidue_cyclic_subfield K D
  let := residueGeneratorField K D (b : D)
  exact ⟨b, hsep, hsurj,
    hdim.trans (localDivisionResidue_finrank_eq_reducedDegree K D), hgal, hcyc⟩

/-- Choose an original integral generator of a cyclic full-residue field of reduced degree. -/
def localDivisionCyclicReducedDegreeGenerator : (localReducedNormValuation K D).integer :=
  Classical.choose (exists_localDivision_fullResidue_reducedDegree_cyclic_subfield K D)

/-- All properties of the chosen original cyclic reduced-degree generator. -/
theorem localDivisionCyclicReducedDegreeGenerator_spec :
    let b := localDivisionCyclicReducedDegreeGenerator K D
    letI := residueGeneratorField K D (b : D)
    IsSeparable K (b : D) ∧
      Function.Surjective (localDivisionSubfieldResidueMap K D
        (residueGeneratorSubalgebra K D (b : D)).val) ∧
      Module.finrank K (residueGeneratorSubalgebra K D (b : D)) =
        CentralSimple.reducedDegree K D ∧
      IsGalois K (residueGeneratorSubalgebra K D (b : D)) ∧
      IsCyclic (residueGeneratorSubalgebra K D (b : D) ≃ₐ[K]
        residueGeneratorSubalgebra K D (b : D)) :=
  Classical.choose_spec (exists_localDivision_fullResidue_reducedDegree_cyclic_subfield K D)

end Langlands.CentralDivision
