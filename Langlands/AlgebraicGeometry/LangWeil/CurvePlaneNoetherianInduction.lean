import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Noetherian induction for uniform bounds over fields

Let `A` be a Noetherian ring and let `Φ B κ` be a property of a natural number `B` and a field
`κ` with an `A`-algebra structure, monotone in `B`. If for every prime `p` of `A` there are an
element `a ∉ p` and a bound `B` that work for all fields killing `p` but not `a`, then one bound
works for all fields.
-/

universe u v

namespace Langlands.AlgebraicGeometry.LangWeil.CurvePlane

/-- Noetherian induction on the base ring: local bounds on all locally closed sets
`V(p) ∩ D(a)` give one global bound. -/
theorem exists_uniform_of_forall_prime {A : Type u} [CommRing A] [IsNoetherianRing A]
    (Φ : ℕ → (κ : Type v) → [Field κ] → [Algebra A κ] → Prop)
    (hmono : ∀ (B B' : ℕ) (κ : Type v) [Field κ] [Algebra A κ], B ≤ B' → Φ B κ → Φ B' κ)
    (hloc : ∀ p : Ideal A, p.IsPrime → ∃ a ∉ p, ∃ B : ℕ, ∀ (κ : Type v) [Field κ] [Algebra A κ],
      (∀ x ∈ p, algebraMap A κ x = 0) → algebraMap A κ a ≠ 0 → Φ B κ) :
    ∃ B : ℕ, ∀ (κ : Type v) [Field κ] [Algebra A κ], Φ B κ := by
  classical
  suffices H : ∀ I : Ideal A, ∃ B : ℕ, ∀ (κ : Type v) [Field κ] [Algebra A κ],
      (∀ x ∈ I, algebraMap A κ x = 0) → Φ B κ by
    obtain ⟨B, hB⟩ := H ⊥
    exact ⟨B, fun κ _ _ => hB κ fun x hx => by rw [(Submodule.mem_bot A).mp hx, map_zero]⟩
  intro I
  induction I using WellFoundedGT.induction with
  | _ I ih =>
  by_cases hI : I = ⊤
  · refine ⟨0, fun κ _ _ hκ => ?_⟩
    exact absurd ((map_one (algebraMap A κ)).symm.trans (hκ 1 (hI ▸ Submodule.mem_top)))
      one_ne_zero
  have key : ∀ q ∈ I.minimalPrimes, ∃ B : ℕ, ∀ (κ : Type v) [Field κ] [Algebra A κ],
      (∀ x ∈ q, algebraMap A κ x = 0) → Φ B κ := by
    intro q hq
    have hqp : q.IsPrime := hq.1.1
    obtain ⟨a, ha, B₁, hB₁⟩ := hloc q hqp
    have hlt : I < q ⊔ Ideal.span {a} := by
      refine lt_of_le_of_ne (hq.1.2.trans le_sup_left) fun h => ha ?_
      have hmem : a ∈ q ⊔ Ideal.span {a} :=
        Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
      exact hq.1.2 (h ▸ hmem)
    obtain ⟨B₂, hB₂⟩ := ih _ hlt
    refine ⟨max B₁ B₂, fun κ _ _ hκ => ?_⟩
    by_cases hκa : algebraMap A κ a = 0
    · refine hmono _ _ κ (le_max_right _ _) (hB₂ κ fun x hx => ?_)
      have hle : q ⊔ Ideal.span {a} ≤ RingHom.ker (algebraMap A κ) := by
        refine sup_le (fun y hy => hκ y hy) ?_
        rw [Ideal.span_le, Set.singleton_subset_iff]
        exact hκa
      exact hle hx
    · exact hmono _ _ κ (le_max_left _ _) (hB₁ κ hκ hκa)
  choose! B hB using key
  have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing A I
  refine ⟨hfin.toFinset.sup B, fun κ _ _ hκ => ?_⟩
  have hker : I ≤ RingHom.ker (algebraMap A κ) := fun x hx => hκ x hx
  have := RingHom.ker_isPrime (algebraMap A κ)
  obtain ⟨q, hq, hqle⟩ := Ideal.exists_minimalPrimes_le hker
  exact hmono _ _ κ (Finset.le_sup (hfin.mem_toFinset.mpr hq))
    (hB q hq κ fun x hx => hqle hx)

end Langlands.AlgebraicGeometry.LangWeil.CurvePlane
