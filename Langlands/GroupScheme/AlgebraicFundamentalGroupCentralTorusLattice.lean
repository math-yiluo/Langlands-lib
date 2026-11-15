import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Exactness of induced maps on quotient lattices

Two linear-algebra steps of the central-torus exactness proof for algebraic
fundamental groups: exactness of the maps induced on quotients by coroot images,
and transfer of exactness along comparison isomorphisms. -/

namespace Langlands.GroupScheme.AlgebraicFundamentalGroup

section LatticeQuotient

variable {R A B C SB SC : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C]
  [AddCommGroup SB] [Module R SB] [AddCommGroup SC] [Module R SC]

/-- Let `0 → A → B → C → 0` be exact (`α` injective, `ker β = range α`, `β` surjective)
and let `ρB : SB → B`, `ρC : SC → C` be lattice maps with `ρC` injective, related by
a bijection `σ : SB → SC` with `ρC ∘ σ = β ∘ ρB`. Then the maps induced on
`A ⧸ RA → B ⧸ range ρB → C ⧸ range ρC` are injective, surjective and exact. -/
theorem quotient_exact_of_lattice_exact
    (RA : Submodule R A) (RB : Submodule R B) (RC : Submodule R C)
    (α : A →ₗ[R] B) (β : B →ₗ[R] C)
    (ρB : SB →ₗ[R] B) (ρC : SC →ₗ[R] C) (σ : SB →ₗ[R] SC)
    (hRB : RB = LinearMap.range ρB) (hRC : RC = LinearMap.range ρC)
    (hα : Function.Injective α) (hαβ : LinearMap.ker β = LinearMap.range α)
    (hβ : Function.Surjective β) (hσ : Function.Bijective σ)
    (hσρ : ∀ s, ρC (σ s) = β (ρB s)) (hρC : Function.Injective ρC)
    (m₁ : (A ⧸ RA) →ₗ[R] (B ⧸ RB)) (m₂ : (B ⧸ RB) →ₗ[R] (C ⧸ RC))
    (hm₁ : ∀ ν, m₁ (RA.mkQ ν) = RB.mkQ (α ν))
    (hm₂ : ∀ x, m₂ (RB.mkQ x) = RC.mkQ (β x)) :
    Function.Injective m₁ ∧ Function.Surjective m₂ ∧
      LinearMap.range m₁ = LinearMap.ker m₂ := by
  subst hRB hRC
  have hβα : ∀ ν, β (α ν) = 0 := fun ν => by
    have h : α ν ∈ LinearMap.ker β := hαβ ▸ ⟨ν, rfl⟩
    exact h
  refine ⟨?_, ?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨ν, rfl⟩ := RA.mkQ_surjective x
    rw [LinearMap.mem_ker, hm₁, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨s, hs⟩ := hx
    have h0 : σ s = 0 := by
      apply hρC
      rw [hσρ, hs, hβα, map_zero]
    have hs0 : s = 0 := hσ.1 (h0.trans (map_zero σ).symm)
    have hν : ν = 0 := by
      apply hα
      rw [← hs, hs0, map_zero, map_zero]
    rw [hν, map_zero]
    exact Submodule.zero_mem _
  · intro y
    obtain ⟨z, rfl⟩ := (LinearMap.range ρC).mkQ_surjective y
    obtain ⟨x, rfl⟩ := hβ z
    exact ⟨_, hm₂ x⟩
  · ext y
    obtain ⟨x, rfl⟩ := (LinearMap.range ρB).mkQ_surjective y
    constructor
    · rintro ⟨w, hw⟩
      obtain ⟨ν, rfl⟩ := RA.mkQ_surjective w
      rw [hm₁] at hw
      rw [LinearMap.mem_ker, ← hw, hm₂, hβα, map_zero]
    · intro hx
      rw [LinearMap.mem_ker, hm₂, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨t, ht⟩ := hx
      obtain ⟨s, rfl⟩ := hσ.2 t
      have hker : x - ρB s ∈ LinearMap.ker β := by
        rw [LinearMap.mem_ker, map_sub, ← hσρ, ht, sub_self]
      rw [hαβ] at hker
      obtain ⟨ν, hν⟩ := hker
      refine ⟨RA.mkQ ν, ?_⟩
      rw [hm₁, hν, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact ⟨-s, by rw [map_neg, sub_sub_cancel_left]⟩

end LatticeQuotient

section Transfer

variable {R A B B' C C' : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup B'] [Module R B'] [AddCommGroup C] [Module R C]
  [AddCommGroup C'] [Module R C']

/-- Exactness `A → B → C` follows from exactness of `A → B' → C'` when the second
row is obtained from the first by a bijection `κB : B → B'` and an injection
`κC : C → C'` making both squares commute. -/
theorem exact_of_comparison
    (F₁ : A →ₗ[R] B) (F₂ : B →ₗ[R] C) (m₁ : A →ₗ[R] B') (m₂ : B' →ₗ[R] C')
    (κB : B →ₗ[R] B') (κC : C →ₗ[R] C')
    (hκB : Function.Bijective κB) (hκC : Function.Injective κC)
    (h₁ : κB.comp F₁ = m₁) (h₂ : κC.comp F₂ = m₂.comp κB)
    (hm : Function.Injective m₁ ∧ Function.Surjective m₂ ∧
      LinearMap.range m₁ = LinearMap.ker m₂) :
    Function.Injective F₁ ∧ Function.Surjective F₂ ∧
      LinearMap.range F₁ = LinearMap.ker F₂ := by
  have e₁ : ∀ x, κB (F₁ x) = m₁ x := fun x => LinearMap.congr_fun h₁ x
  have e₂ : ∀ x, κC (F₂ x) = m₂ (κB x) := fun x => LinearMap.congr_fun h₂ x
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    apply hm.1
    rw [← e₁, ← e₁, hxy]
  · intro y
    obtain ⟨x', hx'⟩ := hm.2.1 (κC y)
    obtain ⟨x, rfl⟩ := hκB.2 x'
    exact ⟨x, hκC ((e₂ x).trans hx')⟩
  · ext x
    constructor
    · rintro ⟨w, rfl⟩
      rw [LinearMap.mem_ker]
      apply hκC
      have hw : m₁ w ∈ LinearMap.ker m₂ := hm.2.2 ▸ ⟨w, rfl⟩
      rw [e₂, e₁, map_zero]
      exact hw
    · intro hx
      rw [LinearMap.mem_ker] at hx
      have hk : κB x ∈ LinearMap.ker m₂ := by
        rw [LinearMap.mem_ker, ← e₂, hx, map_zero]
      rw [← hm.2.2] at hk
      obtain ⟨w, hw⟩ := hk
      exact ⟨w, hκB.1 ((e₁ w).trans hw)⟩

end Transfer

end Langlands.GroupScheme.AlgebraicFundamentalGroup
