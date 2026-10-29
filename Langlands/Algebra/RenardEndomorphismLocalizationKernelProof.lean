import Langlands.Algebra.RenardEndomorphismLocalizationStatements

/-! # Kernel and power exhaustion of actual endomorphism localization: proofs -/

set_option autoImplicit false

universe u v

namespace Langlands.Renard.EndomorphismLocalization

section

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

/-- `ι z = 0` exactly when some power of `a` kills `z`. -/
theorem iota_eq_zero_iff (a : Module.End R V) (z : V) :
    iota a z = 0 ↔ ∃ n : ℕ, (a ^ n) z = 0 := by
  have h0 : (0 : Localized a) = frac a 0 0 := by
    rw [frac_zero, map_zero]
  rw [← frac_zero, h0, frac_eq_frac_iff]
  simp only [add_zero, map_zero]

/-- The power kernels increase. -/
theorem ker_pow_monotone (a : Module.End R V) :
    Monotone (fun n : ℕ => LinearMap.ker (a ^ n)) := by
  intro m n hmn x hx
  rw [LinearMap.mem_ker] at hx ⊢
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [add_comm m k, pow_add, Module.End.mul_apply, hx, map_zero]

theorem ker_iota_eq_iSup (a : Module.End R V) :
    LinearMap.ker (iota a) = ⨆ n : ℕ, LinearMap.ker (a ^ n) := by
  ext z
  rw [LinearMap.mem_ker, iota_eq_zero_iff,
    Submodule.mem_iSup_of_directed _ (ker_pow_monotone a).directed_le]
  simp only [LinearMap.mem_ker]

theorem iota_injective (a : Module.End R V) (ha : Function.Injective a) :
    Function.Injective (iota a) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  obtain ⟨n, hn⟩ := (iota_eq_zero_iff a z).mp hz
  have hinj : Function.Injective (a ^ n) := by
    rw [Module.End.coe_pow]
    exact ha.iterate n
  exact hinj (hn.trans (map_zero _).symm)

theorem iUnion_range_localizedInv_pow (a : Module.End R V) :
    (⋃ n : ℕ, Set.range ((localizedInv a ^ n).comp (iota a))) =
      (Set.univ : Set (Localized a)) := by
  refine Set.eq_univ_of_forall fun z => ?_
  obtain ⟨w, n, rfl⟩ := frac_surjective a z
  exact Set.mem_iUnion.mpr ⟨n, w, by rw [LinearMap.comp_apply, frac_eq_localizedInv_pow]⟩

end

theorem kernelExhaustionStatements : KernelExhaustionStatements.{u, v} :=
  ⟨⟨fun _ _ _ _ _ a z => iota_eq_zero_iff a z, fun _ _ _ _ _ a => ker_iota_eq_iSup a,
      fun _ _ _ _ _ a => iota_injective a, fun _ _ _ _ _ a => iUnion_range_localizedInv_pow a⟩,
    fun _ _ _ _ _ a =>
      ⟨iota_eq_zero_iff a, ker_iota_eq_iSup a, iota_injective a, iUnion_range_localizedInv_pow a⟩⟩

end Langlands.Renard.EndomorphismLocalization
