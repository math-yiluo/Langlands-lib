import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Noetherian.Orzech
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Rank one reflected from all adic quotients -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe uA uM

namespace Langlands.Algebra.AdicRankOne

variable (A : Type uA) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  (M : Type uM) [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- A finite module over a noetherian local ring is free of rank one if
all its quotients by powers of a proper ideal are free of rank one. -/
theorem nonempty_linearEquiv_of_adicQuotients (J : Ideal A) (hJ : J ≠ ⊤)
    (h : ∀ n : ℕ, Nonempty
      ((M ⧸ (J ^ (n + 1) • (⊤ : Submodule A M))) ≃ₗ[A] (A ⧸ J ^ (n + 1)))) :
    Nonempty (M ≃ₗ[A] A) := by
  have hzero : Nonempty ((M ⧸ (J • (⊤ : Submodule A M))) ≃ₗ[A] (A ⧸ J)) := by
    have h0 := h 0
    change Nonempty ((M ⧸ (J ^ (1 : ℕ) • (⊤ : Submodule A M))) ≃ₗ[A]
      (A ⧸ J ^ (1 : ℕ))) at h0
    rw [pow_one] at h0
    exact h0
  let ezero := hzero.some
  obtain ⟨m, hm⟩ := (J • (⊤ : Submodule A M)).mkQ_surjective (ezero.symm (J.mkQ 1))
  let g : A →ₗ[A] M := LinearMap.toSpanSingleton A M m
  have hgsurj : Function.Surjective g := by
    apply LinearMap.surjective_of_surjective_comp_mkQ g J
      ((IsLocalRing.le_maximalIdeal hJ).trans (IsLocalRing.maximalIdeal_le_jacobson ⊥))
    intro y
    obtain ⟨a, ha⟩ := J.mkQ_surjective (ezero y)
    refine ⟨a, ezero.injective ?_⟩
    change ezero ((J • (⊤ : Submodule A M)).mkQ (a • m)) = ezero y
    rw [map_smul, hm, map_smul, ezero.apply_symm_apply]
    calc
      a • J.mkQ 1 = J.mkQ (a • (1 : A)) := (J.mkQ.map_smul a 1).symm
      _ = ezero y := by simpa only [smul_eq_mul, mul_one] using ha
  have hginj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot]
    apply bot_unique
    intro a ha
    have hga : g a = 0 := ha
    have haJ : ∀ n : ℕ, a ∈ J ^ (n + 1) := by
      intro n
      let P : Submodule A M := J ^ (n + 1) • ⊤
      let gn : (A ⧸ J ^ (n + 1)) →ₗ[A] (M ⧸ P) :=
        (J ^ (n + 1)).liftQ (P.mkQ.comp g) (by
          intro r hr
          apply LinearMap.mem_ker.mpr
          change P.mkQ (r • m) = 0
          exact (Submodule.Quotient.mk_eq_zero _).mpr
            (Submodule.smul_mem_smul hr (Submodule.mem_top : m ∈ (⊤ : Submodule A M))))
      have hgnsurj : Function.Surjective gn := by
        intro z
        obtain ⟨y, rfl⟩ := P.mkQ_surjective z
        obtain ⟨r, rfl⟩ := hgsurj y
        exact ⟨(J ^ (n + 1)).mkQ r, rfl⟩
      let en := (h n).some
      have hgninj : Function.Injective gn :=
        IsNoetherian.injective_of_surjective_of_injective en.symm.toLinearMap gn
          en.symm.injective hgnsurj
      have hq : (J ^ (n + 1)).mkQ a = 0 := by
        apply hgninj
        change P.mkQ (g a) = gn 0
        rw [hga, map_zero, map_zero]
      exact (Submodule.Quotient.mk_eq_zero _).mp hq
    have haInf : a ∈ ⨅ n : ℕ, J ^ n := by
      apply (Submodule.mem_iInf _).mpr
      intro n
      cases n with
      | zero => simp
      | succ n => exact haJ n
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing J hJ] at haInf
    exact haInf
  exact ⟨(LinearEquiv.ofBijective g ⟨hginj, hgsurj⟩).symm⟩

/-- A chosen frame for a finite module whose adic quotients have rank one. -/
def equivOfAdicQuotients (J : Ideal A) (hJ : J ≠ ⊤)
    (h : ∀ n : ℕ, Nonempty
      ((M ⧸ (J ^ (n + 1) • (⊤ : Submodule A M))) ≃ₗ[A] (A ⧸ J ^ (n + 1)))) :
    M ≃ₗ[A] A :=
  (nonempty_linearEquiv_of_adicQuotients A M J hJ h).some

end Langlands.Algebra.AdicRankOne
