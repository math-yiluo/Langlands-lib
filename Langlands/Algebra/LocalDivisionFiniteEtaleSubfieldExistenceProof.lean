import Langlands.Algebra.LocalDivisionFiniteEtaleSubfieldExistenceStatement
import Langlands.Algebra.LocalDivisionFullResidueSubfieldEtaleProof

/-! # An actual embedded field with finite étale integer ring: proof -/

universe u

namespace Langlands.CentralDivision

/-- **A full-residue subfield of reduced degree with finite étale integers.** For every
finite-dimensional central division algebra `D` over a nonarchimedean local field `K`, the
singleton adjoin of some integral element of `D` is a field of reduced degree over `K` with full
residue field whose valuation ring is finite étale over `𝒪[K]`. -/
theorem localDivisionFiniteEtaleSubfieldExistence :
    LocalDivisionFiniteEtaleSubfieldExistenceStatement.{u} :=
  localDivisionFiniteEtaleSubfieldExistence_of_fullResidueEtale
    localDivisionFullResidueSubfieldEtale.{u, u}

end Langlands.CentralDivision
