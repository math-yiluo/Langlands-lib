import Langlands.Algebra.FiniteSignedChamberLatticeStatement
import Langlands.Algebra.FiniteChamberLatticeProof
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Tactic

/-! # Signed bases retain all central lattice directions -/

noncomputable section

namespace Langlands

open scoped BigOperators

namespace SignedChamberLattice

universe uΔ uX

variable {Δ : Type uΔ} [Fintype Δ] {X : Type uX} [AddCommGroup X]

/-- The integral submodule annihilated by every supplied pairing. -/
def pairingKernel (pair : Δ → X →+ ℤ) : Submodule ℤ X where
  carrier := {x | ∀ α, pair α x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy α
    simp [hx α, hy α]
  smul_mem' := by
    intro n x hx α
    simp [hx α]

/-- A separated root-axis family remains independent after adjoining any
independent family in the common kernel. -/
theorem independent_join
    (pair : Δ → X →+ ℤ) (axis : Δ → X)
    (hpos : ∀ α, 0 < pair α (axis α))
    (hzero : ∀ α β, β ≠ α → pair β (axis α) = 0)
    {J : Type*} [Fintype J] (b : J → X)
    (hb : LinearIndependent ℤ b) (hker : ∀ j α, pair α (b j) = 0) :
    LinearIndependent ℤ (Sum.elim axis b) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  have hc' : (∑ α, c (.inl α) • axis α) + ∑ i, c (.inr i) • b i = 0 := by
    simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr] using hc
  have hleft (α : Δ) : c (.inl α) = 0 := by
    have h := congrArg (pair α) hc'
    simp only [map_add, map_sum, map_zsmul, hker, smul_zero, Finset.sum_const_zero,
      add_zero, map_zero] at h
    have he : (∑ β, c (.inl β) • pair α (axis β)) =
        c (.inl α) * pair α (axis α) := by
      rw [Finset.sum_eq_single α]
      · rfl
      · intro β _ hβα
        rw [hzero β α (Ne.symm hβα), smul_zero]
      · simp
    rw [he] at h
    exact (mul_eq_zero.mp h).resolve_right (ne_of_gt (hpos α))
  have hright : ∀ i, c (.inr i) = 0 := by
    apply Fintype.linearIndependent_iff.mp hb
    simpa only [hleft, zero_smul, Finset.sum_const_zero, zero_add] using hc'
  cases j with
  | inl α => exact hleft α
  | inr i => exact hright i

/-- A finite integral basis covers its module by its signed positive orthants. -/
theorem basis_signed_orthant {J : Type*} [Fintype J]
    (b : Module.Basis J ℤ X) (x : X) :
    ∃ (ε : J → Bool) (m : J → ℕ),
      x = ∑ j, m j • (if ε j then b j else -(b j)) := by
  classical
  let a := b.equivFun x
  refine ⟨fun j => decide (0 ≤ a j), fun j => (a j).natAbs, ?_⟩
  have hx : x = ∑ j, a j • b j := by
    simpa only [Module.Basis.equivFun_symm_apply] using
      (b.equivFun.symm_apply_apply x).symm
  rw [hx]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : 0 ≤ a j
  · simp [h, ← natCast_zsmul, abs_of_nonneg h]
  · simp [h, ← natCast_zsmul, abs_of_neg (lt_of_not_ge h)]

end SignedChamberLattice

/-- Finitely many independent orthant charts cover the full chamber lattice,
including the common pairing kernel. -/
theorem finiteSignedChamberLattice.{uΔ, uX} :
    FiniteSignedChamberLatticeStatement.{uΔ, uX} := by
  intro Δ _ X _ _ _ pair hstd
  classical
  obtain ⟨axis, hpos, hzero, hcover⟩ := finiteChamberLattice Δ X pair hstd
  let K := SignedChamberLattice.pairingKernel pair
  obtain ⟨k, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := K)
  let signed : (Fin k → Bool) → Fin k → K :=
    fun ε j => if ε j then b j else -(b j)
  let gen : (Fin k → Bool) → (Δ ⊕ Fin k) → X :=
    fun ε => Sum.elim axis (fun j => (signed ε j : X))
  refine ⟨k, gen, ?_, ?_, fun B => ?_⟩
  · intro ε
    apply SignedChamberLattice.independent_join pair axis hpos hzero
    · have hb : LinearIndependent ℤ (signed ε) := by
        have hs : signed ε =
            (fun j => if ε j then (1 : ℤˣ) else -1) • (b : Fin k → K) := by
          funext j
          by_cases h : ε j = true <;> simp [signed, h, Units.smul_def]
        rw [hs]
        exact b.linearIndependent.units_smul (fun j => if ε j then (1 : ℤˣ) else -1)
      exact hb.map' K.subtype (Submodule.ker_subtype K)
    · intro j α
      exact (signed ε j).property α
  · intro ε j α
    cases j with
    | inl β =>
      change 0 ≤ pair α (axis β)
      by_cases h : α = β
      · subst α
        exact (hpos β).le
      · rw [hzero β α h]
    | inr j =>
      change 0 ≤ pair α (signed ε j : X)
      exact le_of_eq ((signed ε j).property α).symm
  · obtain ⟨R, hR, hr⟩ := hcover B
    refine ⟨R, hR, fun x hx => ?_⟩
    obtain ⟨r, hr, n, z, hz, heq⟩ := hr x hx
    obtain ⟨ε, m, hm⟩ := SignedChamberLattice.basis_signed_orthant b ⟨z, hz⟩
    refine ⟨r, hr, ε, Sum.elim n m, ?_⟩
    have hz' : z = ∑ j, m j • (signed ε j : X) := by
      simpa only [signed, map_sum, map_nsmul, Submodule.subtype_apply] using
        congrArg K.subtype hm
    rw [heq, hz']
    simp only [gen, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    abel

end Langlands
