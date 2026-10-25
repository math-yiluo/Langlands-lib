import Langlands.ClassFieldTheory.Local.PrimeRamificationBreakStatement
import Langlands.ClassFieldTheory.Local.PrimeRamificationArithmeticSupport
import Langlands.ClassFieldTheory.Local.PrimeInertiaBreakSupport

/-! The actual single break of a prime totally ramified p-adic extension. -/

namespace Langlands.LocalClassField

universe u v

/-- Prime total ramification has one actual lower break, positive exactly in
residue-characteristic degree, with the actual inverse-Herbrand formula. -/
theorem primeTotallyRamifiedBreak : PrimeTotallyRamifiedBreak.{u,v} := by
  intro p _ F L _ _ _ _
  dsimp only
  intro hell htot
  have hinertia := inertia_eq_top_of_canonical_totalRamification F L htot
  obtain ⟨t, hpat, hpos⟩ := exists_prime_lowerRamificationGroup_pattern
    F L L.canonicalTopologicalData hell hinertia
  exact ⟨t, hpat,
    hpos.trans (lowerRamificationGroup_one_eq_top_iff_prime_degree F L hell htot),
    herbrandPsi_nat_of_prime_pattern F L L.canonicalTopologicalData hell t hpat⟩

end Langlands.LocalClassField
