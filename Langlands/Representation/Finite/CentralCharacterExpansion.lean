import Langlands.Representation.Classification.ConstituentRelations
import Langlands.Representation.Finite.CharacterCompletenessProof

/-!
# Central characters in the character expansion of a finite class function
-/

noncomputable section

namespace Langlands.FiniteRep.CharacterCompleteness

open Classification VirtualCharacter

variable {G A : Type*} [Group G] [Group A]

/-- The subspace of functions that transform by `ω` under translation by `i`. For a
central `i`, intersecting this with `classFunctions G` specifies a central character
component of the class functions. -/
def centralCovariantFunctions (i : A →* G) (ω : A →* ℂˣ) : Submodule ℂ (G → ℂ) where
  carrier := {f | ∀ z g, f (i z * g) = (ω z : ℂ) * f g}
  zero_mem' := fun z _ => (mul_zero (ω z : ℂ)).symm
  add_mem' := fun hf hk z g => by
    simp only [Pi.add_apply, hf z g, hk z g, mul_add]
  smul_mem' := fun c _ hf z g => by
    simp only [Pi.smul_apply, smul_eq_mul, hf z g, mul_left_comm c (ω z : ℂ)]

theorem mem_centralCovariantFunctions (i : A →* G) (ω : A →* ℂˣ) (f : G → ℂ) :
    f ∈ centralCovariantFunctions i ω ↔ ∀ z g, f (i z * g) = (ω z : ℂ) * f g :=
  Iff.rfl

variable [Fintype G]

/-- If a function transforms by `ω` under central translation, a nonzero irreducible character
coefficient can occur only for a representation whose central action restricts to `ω`. -/
theorem hasScalarCharacter_of_pairing_ne_zero (i : A →* G)
    (hi : ∀ z, i z ∈ Subgroup.center G) (ω : A →* ℂˣ) (f : G → ℂ)
    (hω : f ∈ centralCovariantFunctions i ω)
    (a : IrreducibleClass G) (ha : pairing (character a.1) f ≠ 0) :
    HasScalarCharacter (rep a).ρ i ω := by
  have hcov := (mem_centralCovariantFunctions i ω f).mp hω
  intro z v
  let ρ : Representation ℂ G (rep a) := (rep a).ρ
  let T : ρ.IntertwiningMap ρ :=
    { toLinearMap := ρ (i z)
      isIntertwining' := fun g => by
        change ρ (i z) * ρ g = ρ g * ρ (i z)
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hi z) g] }
  let := isIrreducible_rep a
  obtain ⟨c, hc⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).2 T
  have hz : ρ (i z) = c • 1 := by
    have h := congrArg Representation.IntertwiningMap.toLinearMap hc
    rw [Algebra.algebraMap_eq_smul_one] at h
    exact h.symm
  let χ := (rep a).character
  have hχ (g : G) : χ (g * i z) = c * χ g := by
    change LinearMap.trace ℂ (rep a) (ρ (g * i z)) =
      c * LinearMap.trace ℂ (rep a) (ρ g)
    rw [map_mul, hz, mul_smul_comm, mul_one, map_smul, smul_eq_mul]
  let S := ∑ g : G, χ g⁻¹ * f g
  have hS : S ≠ 0 := by
    rw [character_val, pairing_apply] at ha
    intro h
    exact ha (show (Fintype.card G : ℂ)⁻¹ * S = 0 by rw [h, mul_zero])
  have h : (ω z : ℂ) * S = c * S := calc
    (ω z : ℂ) * S = ∑ g : G, χ g⁻¹ * f (i z * g) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun g _ => by rw [hcov]; ring
    _ = ∑ g : G, c * (χ (i z * g)⁻¹ * f (i z * g)) := by
      apply Finset.sum_congr rfl
      intro g _
      rw [← mul_assoc, ← hχ, mul_inv_rev, inv_mul_cancel_right]
    _ = c * S := by
      rw [Finset.mul_sum]
      exact Fintype.sum_equiv (Equiv.mulLeft (i z)) _ _ fun _ => rfl
  have hcω : (ω z : ℂ) = c := mul_right_cancel₀ hS h
  change ρ (i z) v = (ω z : ℂ) • v
  rw [hz, hcω, LinearMap.smul_apply, Module.End.one_apply]

end Langlands.FiniteRep.CharacterCompleteness
