import Langlands.Correspondence.Laumon.CompletionGaloisProof
import Langlands.Correspondence.Laumon.CompletionRamificationReduction

/-!
# Ramification across the completion: the proof

`HenselianCompletionRamificationStatement` from `henselianCompletionGalois` and
`henselianCompletionRamification_of_galois`.
-/

universe u

namespace Langlands.Henniart.Laumon

/-- **Ramification across the completion.** For a finite field `k`, restriction from the
separable closure of `k((t))` to the separable generic closure of the end field carries the
Library's inertia, residue map, Weil degree, wild inertia, finite lower ramification groups and
absolute upper ramification groups to their henselian counterparts. -/
theorem henselianCompletionRamification : HenselianCompletionRamificationStatement.{u} :=
  henselianCompletionRamification_of_galois henselianCompletionGalois

end Langlands.Henniart.Laumon
