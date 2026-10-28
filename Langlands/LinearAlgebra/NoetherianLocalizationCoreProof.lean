import Langlands.LinearAlgebra.NoetherianLocalizationCoreStatements
import Mathlib.RingTheory.Noetherian.Orzech

/-!
# Proof of the internal Noetherian localization core

Derived ordinary-module prerequisites for Renard 2026, Appendix C.II.
The quotient Hopfian route is an alternative to the source argument.
-/

set_option autoImplicit false

namespace Langlands.LinearAlgebra.NoetherianLocalizationCore

universe uR uM uN

section Noetherian

variable {R : Type uR} {M : Type uM}
  [Ring R] [AddCommGroup M] [Module R M] [IsNoetherian R M]

theorem positive_kernel_exponent (a : Module.End R M) :
    ∃ n : ℕ, 0 < n ∧
      (⨆ m : ℕ, LinearMap.ker (a ^ m)) = LinearMap.ker (a ^ n) ∧
      Disjoint (LinearMap.ker (a ^ n)) (LinearMap.range (a ^ n)) := by
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp
    (a.eventually_iSup_ker_pow_eq.and a.eventually_disjoint_ker_pow_range_pow)
  exact ⟨n + 1, Nat.zero_lt_succ n, hn (n + 1) (Nat.le_succ n)⟩

theorem inverse_preserves (e : M ≃ₗ[R] M) (P : Submodule R M)
    (hP : ∀ x ∈ P, e x ∈ P) :
    ∀ x ∈ P, e.symm x ∈ P := by
  let q : M ⧸ P →ₗ[R] M ⧸ P :=
    P.mapQ P e.toLinearMap (fun x hx => hP x hx)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, rfl⟩ := P.mkQ_surjective y
    refine ⟨P.mkQ (e.symm x), ?_⟩
    change P.mkQ (e (e.symm x)) = P.mkQ x
    rw [e.apply_symm_apply]
  have hqi := IsNoetherian.injective_of_surjective_endomorphism q hq
  intro x hx
  apply (Submodule.Quotient.mk_eq_zero P).mp
  apply hqi
  change P.mkQ (e (e.symm x)) = q 0
  rw [map_zero]
  change (Submodule.Quotient.mk (e (e.symm x)) : M ⧸ P) = 0
  simpa only [e.apply_symm_apply] using
    (Submodule.Quotient.mk_eq_zero P).mpr hx

end Noetherian

section Core

variable {R : Type uR} {M : Type uM} {N : Type uN}
  [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem intertwines_pow (a : Module.End R M) (e : N ≃ₗ[R] N)
    (f : M →ₗ[R] N) (hf : ∀ x, f (a x) = e (f x)) (n : ℕ) (x : M) :
    f ((a ^ n) x) = (e ^ n) (f x) := by
  have h : Function.Semiconj f a e := hf
  simpa only [Module.End.pow_apply, LinearEquiv.pow_apply] using h.iterate_right n x

theorem exhaustion_surjective [IsNoetherian R N]
    (a : Module.End R M) (e : N ≃ₗ[R] N) (f : M →ₗ[R] N)
    (hf : ∀ x, f (a x) = e (f x))
    (hex : ∀ y : N, ∃ (n : ℕ) (x : M), (e ^ n) y = f x) :
    Function.Surjective f := by
  intro y
  obtain ⟨n, x, hx⟩ := hex y
  have hinv := inverse_preserves (e ^ n) (LinearMap.range f)
    (fun z hz => by
      obtain ⟨v, rfl⟩ := hz
      exact ⟨(a ^ n) v, intertwines_pow a e f hf n v⟩)
    ((e ^ n) y) (show (e ^ n) y ∈ LinearMap.range f from ⟨x, hx.symm⟩)
  change y ∈ LinearMap.range f
  simpa only [LinearEquiv.symm_apply_apply] using hinv

theorem localization_core [IsNoetherian R M] [IsNoetherian R N]
    (a : Module.End R M) (e : N ≃ₗ[R] N) (f : M →ₗ[R] N)
    (hf : ∀ x, f (a x) = e (f x))
    (hex : ∀ y : N, ∃ (n : ℕ) (x : M), (e ^ n) y = f x)
    (hnil : ∀ x : M, f x = 0 → ∃ n : ℕ, (a ^ n) x = 0) :
    Function.Surjective f ∧
      ∃ n : ℕ, 0 < n ∧ LinearMap.ker f = LinearMap.ker (a ^ n) ∧
        LinearMap.ker (a ^ n) = LinearMap.ker ((a ^ n) ^ 2) ∧
        LinearMap.range (a ^ n) = LinearMap.range ((a ^ n) ^ 2) := by
  have hsurj := exhaustion_surjective a e f hf hex
  obtain ⟨n, hn, hker, _⟩ := positive_kernel_exponent a
  have hkerf : LinearMap.ker f = LinearMap.ker (a ^ n) := by
    ext x
    constructor
    · intro hx
      obtain ⟨m, hm⟩ := hnil x hx
      rw [← hker]
      exact (le_iSup (fun i : ℕ => LinearMap.ker (a ^ i)) m) hm
    · intro hx
      apply (e ^ n).injective
      rw [← intertwines_pow a e f hf n x, hx, map_zero, map_zero]
  refine ⟨hsurj, n, hn, hkerf, ?_, ?_⟩
  · apply le_antisymm
    · intro x hx
      change (a ^ n) ((a ^ n) x) = 0
      rw [show (a ^ n) x = 0 from hx, map_zero]
    · intro x hx
      rw [← hker]
      apply (le_iSup (fun i : ℕ => LinearMap.ker (a ^ i)) (n + n))
      simpa only [pow_add, pow_two, Module.End.mul_apply] using hx
  · apply le_antisymm
    · rintro y ⟨x, rfl⟩
      obtain ⟨v, hv⟩ := hsurj ((e ^ n).symm (f x))
      have hz : f (x - (a ^ n) v) = 0 := by
        rw [map_sub, intertwines_pow a e f hf n v, hv,
          (e ^ n).apply_symm_apply, sub_self]
      have hk : x - (a ^ n) v ∈ LinearMap.ker (a ^ n) := by
        rw [← hkerf]
        exact hz
      have heq : (a ^ n) ((a ^ n) v) = (a ^ n) x := by
        have hz' : (a ^ n) (x - (a ^ n) v) = 0 := hk
        exact (sub_eq_zero.mp (by simpa only [map_sub] using hz')).symm
      exact ⟨v, by simpa only [pow_two, Module.End.mul_apply] using heq⟩
    · rintro y ⟨x, rfl⟩
      exact ⟨(a ^ n) x, by simp only [pow_two, Module.End.mul_apply]⟩

end Core


/-- All three closed Noetherian localization-core targets. -/
theorem noetherianLocalizationCore :
    NoetherianLocalizationCoreStatement.{uR, uM, uN} := by
  refine ⟨?_, ?_, ?_⟩
  · intro R M _ _ _ _ e P hP
    exact inverse_preserves e P hP
  · intro R M N _ _ _ _ _ _ a e f hf hex
    exact exhaustion_surjective a e f hf hex
  · intro R M N _ _ _ _ _ _ _ a e f hf hex hnil
    exact localization_core a e f hf hex hnil

end Langlands.LinearAlgebra.NoetherianLocalizationCore
