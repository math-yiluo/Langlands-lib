import Langlands.Algebra.LocalDivisionSK1Statement
import Langlands.Algebra.LocalDivisionSK1Reduction
import Langlands.Algebra.LocalDivisionSubfieldCyclic
import Langlands.Algebra.LocalDivisionResidueDegreeProof
import Langlands.Algebra.LocalDivisionUnitMovement

/-! The reduced-norm kernel of a local central division algebra is the commutator subgroup. -/

noncomputable section

namespace Langlands.CentralDivision

universe u

open Langlands.CentralSimple ValuativeRel

/-- Over a nonarchimedean local field, the kernel of the canonical reduced norm on the
units of a finite-dimensional central division algebra is the commutator subgroup. -/
theorem localSK1 : LocalSK1Statement.{u} := by
  intro F _ _ _ _ D _ _ _ _
  obtain ⟨b, -, hsurj, hdim, hgal, hcyc⟩ :=
    exists_localDivision_fullResidue_cyclic_subfield F D
  let := residueGeneratorField F D (b : D)
  have hdeg : Module.finrank F (residueGeneratorSubalgebra F D (b : D)) =
      reducedDegree F D := hdim.trans (localResidueDegree F D)
  exact ker_coefficientNorm_eq_commutator_of_unit_movement
    (residueGeneratorSubalgebra F D (b : D)).val hdeg fun a ha =>
      localDivision_move_unit F D _ hsurj (localResidueDegree F D) a ha

end Langlands.CentralDivision
