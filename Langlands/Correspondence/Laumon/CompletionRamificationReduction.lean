import Langlands.Correspondence.Laumon.CompletionWildInertia

/-!
# Ramification across the completion, from the Galois comparison

`HenselianCompletionRamificationStatement` follows from `HenselianCompletionGaloisStatement`:
clauses 2 and 3 hold outright, clause 1 uses the surjectivity of restriction, and clauses 4, 5
and 6 use that restriction is a homeomorphism.
-/

universe u

namespace Langlands.Henniart.Laumon

/-- **Reduction to the Galois comparison.** If restriction from `k((t))` to the end field is a
homeomorphism for every field `k`, it carries the Library's inertia, residue map, Weil degree,
wild inertia, finite lower groups and absolute upper groups to their henselian counterparts for
every finite field `k`. -/
theorem henselianCompletionRamification_of_galois
    (h : HenselianCompletionGaloisStatement.{u}) :
    HenselianCompletionRamificationStatement.{u} := by
  intro k _ _
  have hr := h k
  exact ⟨absoluteInertia_map_completionRestriction k hr.bijective.surjective,
    exists_constants_residue_equiv k, completionRestriction_localProjection_pow k,
    mem_map_localWildInertia_iff k hr,
    fun L σ i => mem_lowerRamificationGroup_iff_henselianLowerTest hr L σ i,
    fun v _ τ => mem_map_localAbsoluteUpperRamificationGroup_iff hr v τ⟩

end Langlands.Henniart.Laumon
