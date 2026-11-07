import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Invariant principal opens containing a finite orbit -/

namespace Langlands.Algebra.InvariantPrincipalOpen

variable {R : Type*} [CommRing R] {W : Type*} [CommRing W] [Algebra R W]

/-- Prime avoidance: an ideal contained in none of finitely many primes has an
element outside all of them. -/
theorem exists_mem_forall_not_mem {ι : Type*} (s : Finset ι) (P : ι → Ideal W)
    (hP : ∀ i ∈ s, (P i).IsPrime) (J : Ideal W) (hJ : ∀ i ∈ s, ¬ J ≤ P i) :
    ∃ g ∈ J, ∀ i ∈ s, g ∉ P i := by
  classical
  by_contra! h
  have hsub : (J : Set W) ⊆ ⋃ i ∈ (↑s : Set ι), (P i : Set W) := by
    intro g hg
    obtain ⟨i, hi, hgi⟩ := h g hg
    exact Set.mem_biUnion hi hgi
  cases s.eq_empty_or_nonempty with
  | inl hs =>
    subst hs
    obtain ⟨i, hi, _⟩ := h 0 J.zero_mem
    simp at hi
  | inr hs =>
    obtain ⟨a, ha⟩ := hs
    obtain ⟨i, hi, hle⟩ :=
      (Ideal.subset_union_prime a a (fun i hi _ _ => hP i hi)).mp hsub
    exact hJ i hi hle

variable {Γ : Type*} [Group Γ] [Fintype Γ]

/-- The norm `∏ γ, σ γ g` of an element under a finite group of automorphisms. -/
def norm (σ : Γ →* (W ≃ₐ[R] W)) (g : W) : W := ∏ γ, σ γ g

theorem norm_invariant (σ : Γ →* (W ≃ₐ[R] W)) (g : W) (δ : Γ) :
    σ δ (norm σ g) = norm σ g := by
  simp only [norm, map_prod]
  have : ∀ γ, σ δ (σ γ g) = σ (δ * γ) g := by
    intro γ
    rw [map_mul]
    rfl
  simp only [this]
  exact Fintype.prod_equiv (Equiv.mulLeft δ) _ _ (fun γ => rfl)

theorem norm_not_mem (σ : Γ →* (W ≃ₐ[R] W)) {g : W} {P : Ideal W} [P.IsPrime]
    (h : ∀ γ, σ γ g ∉ P) : norm σ g ∉ P := by
  intro hmem
  obtain ⟨γ, _, hγ⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
  exact h γ hγ

theorem dvd_norm (σ : Γ →* (W ≃ₐ[R] W)) (g : W) : g ∣ norm σ g := by
  have h1 : σ 1 g = g := by rw [map_one]; rfl
  conv_lhs => rw [← h1]
  exact Finset.dvd_prod_of_mem (fun γ => σ γ g) (Finset.mem_univ 1)

section Localization

variable (σ : Γ →* (W ≃ₐ[R] W)) {N : W} (hN : ∀ γ, σ γ N = N)

include hN
omit [Fintype Γ]

theorem map_powers_eq (γ : Γ) :
    (Submonoid.powers N).map (σ γ).toRingEquiv.toMonoidHom = Submonoid.powers N := by
  rw [Submonoid.map_powers]
  congr 1
  exact hN γ

/-- The induced action on the localization at an invariant element. -/
noncomputable def awayEquiv (γ : Γ) : Localization.Away N ≃+* Localization.Away N :=
  IsLocalization.ringEquivOfRingEquiv (Localization.Away N) (Localization.Away N)
    (σ γ).toRingEquiv (map_powers_eq σ hN γ)

theorem awayEquiv_algebraMap (γ : Γ) (w : W) :
    awayEquiv σ hN γ (algebraMap W (Localization.Away N) w) =
      algebraMap W (Localization.Away N) (σ γ w) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ w

/-- The action on the localization at an invariant element, as a group homomorphism. -/
noncomputable def awayAction : Γ →* (Localization.Away N ≃+* Localization.Away N) where
  toFun := awayEquiv σ hN
  map_one' := by
    apply RingEquiv.ext
    intro x
    have : (awayEquiv σ hN 1 : Localization.Away N →+* Localization.Away N) =
        RingHom.id _ := by
      apply IsLocalization.ringHom_ext (Submonoid.powers N)
      ext w
      simp [awayEquiv_algebraMap]
    exact congrArg (fun f => f x) this
  map_mul' g h := by
    apply RingEquiv.ext
    intro x
    have : (awayEquiv σ hN (g * h) : Localization.Away N →+* Localization.Away N) =
        (awayEquiv σ hN g : Localization.Away N →+* Localization.Away N).comp
          (awayEquiv σ hN h) := by
      apply IsLocalization.ringHom_ext (Submonoid.powers N)
      ext w
      simp [awayEquiv_algebraMap, map_mul]
    exact congrArg (fun f => f x) this

theorem awayAction_algebraMap (γ : Γ) (w : W) :
    awayAction σ hN γ (algebraMap W (Localization.Away N) w) =
      algebraMap W (Localization.Away N) (σ γ w) :=
  awayEquiv_algebraMap σ hN γ w

end Localization

end Langlands.Algebra.InvariantPrincipalOpen
