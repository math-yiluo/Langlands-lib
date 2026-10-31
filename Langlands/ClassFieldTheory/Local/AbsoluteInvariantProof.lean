import Langlands.ClassFieldTheory.Local.AbsoluteInvariantAssembly
import Langlands.ClassFieldTheory.Local.UnramifiedH2Proof
import Langlands.ClassFieldTheory.Local.ClosureInflationNaturalityProof
import Langlands.ClassFieldTheory.Local.UnramifiedInvariantInflationProof
import Langlands.ClassFieldTheory.Local.UnramifiedBaseChangeProof
import Langlands.ClassFieldTheory.Local.UnramifiedInvariantBaseChangeProof

/-! # Absolute local invariants and restriction by degree -/

namespace Langlands.ClassFieldTheory.Local

universe u

/-- The actual absolute local H2 groups admit a simultaneous family of additive
invariant equivalences satisfying restriction by every finite extension degree. -/
theorem absoluteInvariantExistence : AbsoluteInvariantExistence.{u} :=
  AbsoluteInvariantAssembly.absoluteInvariantExistence_of_finite_stages
    unramifiedH2Exhaustion.{u}
    closureInflationTowerCompatibility.{u}
    unramifiedInvariantInflationCompatibility.{u}
    unramifiedBaseChangeStageExistence.{u}
    closureInflationBaseChangeCompatibility.{u}
    unramifiedInvariantBaseChangeCompatibility.{u}

end Langlands.ClassFieldTheory.Local
