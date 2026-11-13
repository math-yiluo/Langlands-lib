import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.GroupAction.Basic

/-! # Twisting a semilinear permutation action by a cocycle -/

noncomputable section

namespace Langlands.Geometry.Building.SemilinearCocycleAction

universe uΓ uH uX uk uK

variable {Γ : Type uΓ} [Group Γ] {H : Type uH} [Group H]
  {X : Type uX} [MulAction H X]
  (ρ : Γ →* MulAut H) (A : Γ →* Equiv.Perm X)
  (hA : ∀ σ g x, A σ (g • x) = ρ σ g • A σ x)
  (c : Γ → H) (hc : ∀ σ τ, c (σ * τ) = c σ * ρ σ (c τ))

include hc in
/-- A crossed homomorphism takes the identity to the identity. -/
theorem cocycle_one : c 1 = 1 := by
  have h : c 1 = c 1 * c 1 := by
    simpa only [one_mul, map_one, MulAut.one_apply] using hc 1 1
  exact (mul_left_cancel ((mul_one (c 1)).trans h)).symm

include hA hc in
/-- The twisted maps satisfy the multiplication law on the original carrier. -/
theorem twist_mul (σ τ : Γ) (x : X) :
    c (σ * τ) • A (σ * τ) x = c σ • A σ (c τ • A τ x) := by
  rw [hc, hA, mul_smul, map_mul, Equiv.Perm.mul_apply]

/-- The cocycle twist, as genuine permutations of the same original carrier. -/
def action : Γ →* Equiv.Perm X where
  toFun σ :=
    { toFun x := c σ • A σ x
      invFun x := c σ⁻¹ • A σ⁻¹ x
      left_inv x := by
        change c σ⁻¹ • A σ⁻¹ (c σ • A σ x) = x
        rw [← twist_mul ρ A hA c hc, inv_mul_cancel, cocycle_one ρ c hc,
          map_one, Equiv.Perm.one_apply, one_smul]
      right_inv x := by
        change c σ • A σ (c σ⁻¹ • A σ⁻¹ x) = x
        rw [← twist_mul ρ A hA c hc, mul_inv_cancel, cocycle_one ρ c hc,
          map_one, Equiv.Perm.one_apply, one_smul] }
  map_one' := Equiv.ext fun x => by
    change c 1 • A 1 x = x
    rw [cocycle_one ρ c hc, map_one, Equiv.Perm.one_apply, one_smul]
  map_mul' σ τ := Equiv.ext (twist_mul ρ A hA c hc σ τ)

@[simp] theorem action_apply (σ : Γ) (x : X) :
    action ρ A hA c hc σ x = c σ • A σ x := rfl

section FiniteLevel

variable (k : Type uk) (K : Type uK) [Field k] [Field K] [Algebra k K]
  (ρK : (K ≃ₐ[k] K) →* MulAut H)
  (cK : (K ≃ₐ[k] K) → H)
  (hcK : ∀ σ τ, cK (σ * τ) = cK σ * ρK σ (cK τ))

include hcK in
/-- A cocycle trivial on the pointwise fixer of a finite subextension has finite range.
The intermediate field need not be normal or separable. -/
theorem finite_range_of_finite_fixing_field
    (E : IntermediateField k K) [FiniteDimensional k E]
    (hE : ∀ σ ∈ E.fixingSubgroup, cK σ = 1) :
    (Set.range cK).Finite := by
  classical
  let q : (K ≃ₐ[k] K) → (E →ₐ[k] K) := fun σ => σ.toAlgHom.comp E.val
  have hq : ∀ σ τ, q σ = q τ → cK σ = cK τ := by
    intro σ τ h
    have hfix : τ⁻¹ * σ ∈ E.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      have h2 := DFunLike.congr_fun h ⟨y, hy⟩
      change σ y = τ y at h2
      rw [AlgEquiv.mul_apply, h2, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    calc
      cK σ = cK (τ * (τ⁻¹ * σ)) := by rw [mul_inv_cancel_left]
      _ = cK τ := by rw [hcK, hE _ hfix, map_one, mul_one]
  let f : Set.range q → H := fun y => cK y.2.choose
  refine (Set.finite_range f).subset ?_
  rintro _ ⟨σ, rfl⟩
  refine ⟨⟨q σ, σ, rfl⟩, ?_⟩
  exact hq _ _ (⟨q σ, σ, rfl⟩ : Set.range q).2.choose_spec

end FiniteLevel

/-- A coefficient-fixed point has finite twisted orbit whenever the cocycle has
finite range. -/
theorem finite_orbit_of_fixed (x : X) (hx : ∀ σ, A σ x = x)
    (hfin : (Set.range c).Finite) :
    (Set.range fun σ => action ρ A hA c hc σ x).Finite := by
  refine (hfin.image fun g : H => g • x).subset ?_
  rintro _ ⟨σ, rfl⟩
  exact ⟨c σ, ⟨σ, rfl⟩, by
    change c σ • x = c σ • A σ x
    rw [hx σ]⟩

end Langlands.Geometry.Building.SemilinearCocycleAction
