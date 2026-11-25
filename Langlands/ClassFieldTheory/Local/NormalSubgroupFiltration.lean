import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.RamificationQuotients

/-!
# Antitone filtrations by normal subgroups

This file belongs to the Library. The ramification theory of the NYLL library works with
`RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration G`: a sequence
`lower : ℕ → Subgroup G` of normal subgroups of a group `G` (`lower_normal`), decreasing
(`antitone : m ≤ n → lower n ≤ lower m`). The Library uses this structure for towers of open
normal subgroups (`Langlands.CongruenceTower` of the module `Langlands.Shimura.DefiniteFormsTower`).
This file states its two laws in Mathlib's vocabulary:

* `antitone_lower F : Antitone F.lower`;
* `normal_lower F n : (F.lower n).Normal`.
-/

universe u

namespace Langlands.ClassFieldTheory.Local.NormalSubgroupFiltration

open RamificationTheory.DiscreteValuationField

variable {G : Type u} [Group G] (F : AntitoneNormalSubgroupFiltration G)

/-- The members of an antitone filtration by normal subgroups form an antitone sequence of
subgroups. -/
theorem antitone_lower : Antitone F.lower :=
  fun _ _ h => F.antitone h

/-- Every member of an antitone filtration by normal subgroups is a normal subgroup. -/
theorem normal_lower (n : ℕ) : (F.lower n).Normal :=
  F.lower_normal n

end Langlands.ClassFieldTheory.Local.NormalSubgroupFiltration
