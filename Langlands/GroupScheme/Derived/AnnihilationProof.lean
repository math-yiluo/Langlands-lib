import Langlands.GroupScheme.Derived.AnnihilationCommutativeProof
import Langlands.GroupScheme.Derived.AnnihilationCharacterProof

/-! # Proof: derived subgroups are annihilated by commutative targets -/

universe u

namespace Langlands.GroupScheme

/-- Milne 6.19(d): both the homomorphism form and the character form. -/
theorem derivedAnnihilation : DerivedAnnihilationStatement.{u} :=
  ⟨derivedCommutativeAnnihilation, derivedCharacterAnnihilation⟩

end Langlands.GroupScheme
