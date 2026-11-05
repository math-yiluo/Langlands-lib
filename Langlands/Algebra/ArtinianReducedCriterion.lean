import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Nilpotent.Basic

/-! # A reducedness criterion for commutative Artinian rings -/

noncomputable section

namespace Langlands.ArtinianReducedCriterion

variable {R : Type*} [CommRing R]

/-- A nilpotent ideal contained in its square is zero. -/
theorem eq_bot_of_isNilpotent_le_sq (I : Ideal R) (hI : IsNilpotent I)
    (hle : I ≤ I ^ 2) : I = ⊥ := by
  have hid : IsIdempotentElem I :=
    le_antisymm Ideal.mul_le_left (by simpa only [pow_two] using hle)
  exact hid.eq_zero_of_isNilpotent hI

/-- To prove an Artinian ring reduced it suffices that its nilradical lies
in the square of every maximal ideal. -/
theorem isReduced_of_nilradical_le_maximal_sq [IsArtinianRing R]
    (h : ∀ m : MaximalSpectrum R, nilradical R ≤ m.asIdeal ^ 2) : IsReduced R := by
  have hN : nilradical R ≤ nilradical R ^ 2 := by
    rw [IsArtinianRing.nilradical_pow_eq_iInf]
    exact le_iInf h
  have hz := eq_bot_of_isNilpotent_le_sq (nilradical R)
    IsArtinianRing.isNilpotent_nilradical hN
  exact ⟨fun x hx => by
    have hxN : x ∈ nilradical R := hx
    simpa only [hz, Ideal.mem_bot] using hxN⟩

end Langlands.ArtinianReducedCriterion
