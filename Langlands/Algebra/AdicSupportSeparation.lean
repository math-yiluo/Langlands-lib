import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Finiteness.Ideal

/-! # Adic separation for submodules supported on a closed locus -/

noncomputable section

universe u v

namespace Langlands.Algebra.AdicSupportSeparation

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Artin–Rees separates a submodule annihilated by a power of the adic ideal
from a sufficiently deep term of the ambient filtration. -/
theorem exists_inf_pow_eq_bot_of_power_annihilates
    (J : Ideal R) (N : Submodule R M) (e : ℕ) (he : J ^ e • N = ⊥) :
    ∃ n : ℕ, 0 < n ∧ N ⊓ (J ^ (n + 1) • ⊤) = ⊥ := by
  obtain ⟨k, hk⟩ := J.exists_pow_inf_eq_pow_smul N
  refine ⟨k + e + 1, by omega, ?_⟩
  rw [inf_comm, hk _ (by omega)]
  apply le_antisymm ?_ bot_le
  exact (Submodule.smul_mono (Ideal.pow_le_pow_right (by omega : e ≤ k + e + 1 + 1 - k))
    inf_le_right).trans_eq he

/-- Support in the closed locus of `J` yields a positive stage separating `N`
from the ambient `J`-adic filtration. -/
theorem exists_inf_pow_eq_bot_of_support
    (J : Ideal R) (N : Submodule R M)
    (hs : Module.support R N ⊆ PrimeSpectrum.zeroLocus (J : Set R)) :
    ∃ n : ℕ, 0 < n ∧ N ⊓ (J ^ (n + 1) • ⊤) = ⊥ := by
  have hrad : J ≤ N.annihilator.radical := by
    apply (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff N.annihilator J).mp
    simpa only [Submodule.annihilator, ← Module.support_eq_zeroLocus] using hs
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
    (IsNoetherian.noetherian J)
  exact exists_inf_pow_eq_bot_of_power_annihilates J N e
    (Submodule.le_annihilator_iff.mp he)

/-- A chosen positive stage of adic separation. -/
def separationIndex (J : Ideal R) (N : Submodule R M)
    (hs : Module.support R N ⊆ PrimeSpectrum.zeroLocus (J : Set R)) : ℕ :=
  (exists_inf_pow_eq_bot_of_support J N hs).choose

theorem separationIndex_pos (J : Ideal R) (N : Submodule R M)
    (hs : Module.support R N ⊆ PrimeSpectrum.zeroLocus (J : Set R)) :
    0 < separationIndex J N hs :=
  (exists_inf_pow_eq_bot_of_support J N hs).choose_spec.1

theorem inf_pow_separationIndex_eq_bot (J : Ideal R) (N : Submodule R M)
    (hs : Module.support R N ⊆ PrimeSpectrum.zeroLocus (J : Set R)) :
    N ⊓ (J ^ (separationIndex J N hs + 1) • ⊤) = ⊥ :=
  (exists_inf_pow_eq_bot_of_support J N hs).choose_spec.2

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- A later submodule vanishing modulo a separating power is zero. -/
theorem eq_bot_of_le_and_le_pow (J : Ideal R) (N P : Submodule R M) (n : ℕ)
    (hsep : N ⊓ (J ^ (n + 1) • ⊤) = ⊥)
    (hPN : P ≤ N) (hP : P ≤ J ^ (n + 1) • ⊤) : P = ⊥ := by
  exact le_antisymm ((le_inf hPN hP).trans_eq hsep) bot_le

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- Quotient-map form of the later-submodule criterion. -/
theorem eq_bot_of_le_and_quotient_image_eq_bot (J : Ideal R)
    (N P : Submodule R M) (n : ℕ) (hsep : N ⊓ (J ^ (n + 1) • ⊤) = ⊥)
    (hPN : P ≤ N)
    (hP : P.map (Submodule.mkQ (J ^ (n + 1) • ⊤)) = ⊥) : P = ⊥ := by
  apply eq_bot_of_le_and_le_pow J N P n hsep hPN
  simpa only [Submodule.comap_bot, Submodule.ker_mkQ] using
    Submodule.map_le_iff_le_comap.mp hP.le

/-- Ideal form of support-based adic separation. -/
theorem exists_ideal_inf_pow_eq_bot_of_support (J I : Ideal R)
    (hs : Module.support R I ⊆ PrimeSpectrum.zeroLocus (J : Set R)) :
    ∃ n : ℕ, 0 < n ∧ I ⊓ J ^ (n + 1) = ⊥ := by
  obtain ⟨n, hn, hsep⟩ := exists_inf_pow_eq_bot_of_support J I hs
  exact ⟨n, hn, by simpa only [smul_eq_mul, Ideal.mul_top] using hsep⟩

omit [IsNoetherianRing R] [Module.Finite R M] in
/-- If a later ideal is contained in a separated ideal and vanishes in the
quotient by the separating power, it is zero. -/
theorem ideal_eq_bot_of_le_and_quotient_image_eq_bot (J I K : Ideal R) (n : ℕ)
    (hsep : I ⊓ J ^ (n + 1) = ⊥) (hKI : K ≤ I)
    (hK : K.map (Ideal.Quotient.mk (J ^ (n + 1))) = ⊥) : K = ⊥ := by
  have hKJ : K ≤ J ^ (n + 1) := by
    simpa only [Ideal.mk_ker] using (Ideal.map_eq_bot_iff_le_ker _).mp hK
  exact le_antisymm ((le_inf hKI hKJ).trans_eq hsep) bot_le

end Langlands.Algebra.AdicSupportSeparation
