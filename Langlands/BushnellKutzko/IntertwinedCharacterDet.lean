import Langlands.BushnellKutzko.IntertwinedCharacterDetStatement
import Langlands.BushnellKutzko.IntertwinedUnitCharacter

/-! # Characters of `U^{m+1}(𝔄)` intertwined by all of `G` factor through the determinant

Bushnell–Kutzko 1993, Lemma (2.4.11), character part, for an arbitrary group homomorphism
`χ : U^{m+1}(𝔄) → ℂˣ`. The theorem `intertwinedUnitCharacter` proves the same factorization
for `U^k(𝔄)` with `1 ≤ k`, stated pointwise; this file specializes it at `k = m + 1` and turns
the pointwise identity into an equality of homomorphisms.
-/

namespace Langlands.BushnellKutzko

universe uF uV

/-- **BK93 (2.4.11), character part.** A homomorphism `χ : U^{m+1}(𝔄) →* ℂˣ` intertwined by
every element of `G = (Module.End F V)ˣ` is `φ ∘ det` for a homomorphism `φ` on the image of
the determinant on `U^{m+1}(𝔄)`. -/
theorem intertwinedCharacterDet : IntertwinedCharacterDetStatement.{uF, uV} := by
  intro F _ _ _ _ V _ _ L m χ hI
  obtain ⟨η, hη⟩ := intertwinedUnitCharacter F V L (m + 1) (Nat.succ_pos m) χ hI
  exact ⟨η, MonoidHom.ext hη⟩

end Langlands.BushnellKutzko
