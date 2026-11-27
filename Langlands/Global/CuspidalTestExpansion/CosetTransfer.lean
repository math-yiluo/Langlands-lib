import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Tactic.Group

/-! # Transfer of coset sums along a homomorphism -/

set_option autoImplicit false

namespace Langlands.Global.CosetTransfer

variable {Γ H : Type*} [Group Γ] [Group H] (φ : Γ →* H) (Λ : Subgroup Γ) (A B : Subgroup H)

/-- Let `φ : Γ →* H` satisfy `φ(Γ) ⊆ B` and `φ⁻¹(A) = Λ`, and suppose every point of `B` is a
product `a * φ x` with `a ∈ A`. Then `[x] ↦ [φ x]` is a bijection `Λ \ Γ ≃ (A ∩ B) \ B` of right
coset spaces (the codomain is `Quotient (rightRel (A.subgroupOf B))`). -/
noncomputable def cosetEquiv (hφB : ∀ x, φ x ∈ B) (hpre : ∀ x, φ x ∈ A ↔ x ∈ Λ)
    (hsurj : ∀ b ∈ B, ∃ a ∈ A, ∃ x, b = a * φ x) :
    Quotient (QuotientGroup.rightRel Λ) ≃ Quotient (QuotientGroup.rightRel (A.subgroupOf B)) :=
  Equiv.ofBijective
    (Quotient.map' (fun x => (⟨φ x, hφB x⟩ : B)) (fun x y h => by
      rw [QuotientGroup.rightRel_apply] at h ⊢
      rw [Subgroup.mem_subgroupOf]
      change φ y * (φ x)⁻¹ ∈ A
      rw [← map_inv, ← map_mul]
      exact (hpre _).mpr h))
    (by
      constructor
      · intro c d h
        induction c using Quotient.inductionOn with
        | _ x =>
        induction d using Quotient.inductionOn with
        | _ y =>
        have h' : QuotientGroup.rightRel (A.subgroupOf B) (⟨φ x, hφB x⟩ : B) ⟨φ y, hφB y⟩ :=
          Quotient.exact h
        rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf] at h'
        apply Quotient.sound
        show QuotientGroup.rightRel Λ x y
        rw [QuotientGroup.rightRel_apply]
        apply (hpre _).mp
        change φ y * (φ x)⁻¹ ∈ A at h'
        rwa [map_mul, map_inv]
      · intro c
        induction c using Quotient.inductionOn with
        | _ b =>
        obtain ⟨a, ha, x, hx⟩ := hsurj b b.property
        refine ⟨Quotient.mk _ x, ?_⟩
        apply Quotient.sound
        show QuotientGroup.rightRel (A.subgroupOf B) (⟨φ x, hφB x⟩ : B) b
        rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
        change (b : H) * (φ x)⁻¹ ∈ A
        rw [hx, mul_inv_cancel_right]
        exact ha)

theorem cosetEquiv_out (hφB : ∀ x, φ x ∈ B) (hpre : ∀ x, φ x ∈ A ↔ x ∈ Λ)
    (hsurj : ∀ b ∈ B, ∃ a ∈ A, ∃ x, b = a * φ x) (c : Quotient (QuotientGroup.rightRel Λ)) :
    ∃ a ∈ A, (((cosetEquiv φ Λ A B hφB hpre hsurj c).out : B) : H) = a * φ c.out := by
  have h : cosetEquiv φ Λ A B hφB hpre hsurj c = Quotient.mk _ ⟨φ c.out, hφB c.out⟩ := by
    have hc : c = Quotient.mk _ c.out := (Quotient.out_eq c).symm
    calc cosetEquiv φ Λ A B hφB hpre hsurj c
        = cosetEquiv φ Λ A B hφB hpre hsurj (Quotient.mk _ c.out) := congrArg _ hc
      _ = Quotient.mk _ ⟨φ c.out, hφB c.out⟩ := rfl
  have h' : QuotientGroup.rightRel (A.subgroupOf B)
      (cosetEquiv φ Λ A B hφB hpre hsurj c).out ⟨φ c.out, hφB c.out⟩ :=
    Quotient.exact ((Quotient.out_eq (cosetEquiv φ Λ A B hφB hpre hsurj c)).trans h)
  rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf] at h'
  refine ⟨_, A.inv_mem h', ?_⟩
  change _ = ((φ c.out * ((cosetEquiv φ Λ A B hφB hpre hsurj c).out : H)⁻¹)⁻¹) * φ c.out
  group

/-- Under the hypotheses of `cosetEquiv`, sums over `(A ∩ B) \ B` of a left `A`-invariant
function become sums over `Λ \ Γ`. -/
theorem tsum_cosetEquiv {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (hφB : ∀ x, φ x ∈ B) (hpre : ∀ x, φ x ∈ A ↔ x ∈ Λ)
    (hsurj : ∀ b ∈ B, ∃ a ∈ A, ∃ x, b = a * φ x) (f : H → E) (hf : ∀ a ∈ A, ∀ h, f (a * h) = f h)
    (y : H) :
    ∑' c : Quotient (QuotientGroup.rightRel Λ), f (φ c.out * y) =
      ∑' c : Quotient (QuotientGroup.rightRel (A.subgroupOf B)), f ((c.out : H) * y) := by
  rw [← (cosetEquiv φ Λ A B hφB hpre hsurj).tsum_eq]
  refine tsum_congr fun c => ?_
  obtain ⟨a, ha, hc⟩ := cosetEquiv_out φ Λ A B hφB hpre hsurj c
  rw [hc, mul_assoc, hf a ha]

end Langlands.Global.CosetTransfer
