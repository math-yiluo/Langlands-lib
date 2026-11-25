/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.Data.Fintype.Option

/-!
# Reflexive modules: finite products and cyclic modules

## Main statements

- `Module.IsReflexive.pi`: a finite product of reflexive modules is reflexive.
- `Module.isReflexive_quotient_of_colon`: a cyclic module `A ⧸ J` over a commutative ring is
  reflexive as soon as `J` is its own double annihilator and every linear map from the
  annihilator of `J` to `A` is a multiplication. Both conditions hold for every ideal of a
  self-injective ring with the double annihilator property, such as `𝒪 ⧸ ϖⁿ` for a discrete
  valuation ring `𝒪`.
-/

@[expose] public section

open Module

namespace Module

variable {A : Type*} [CommRing A]

/-- A module over a subsingleton-module is reflexive: all three of `M`, its dual and its double
dual are trivial. -/
lemma IsReflexive.of_subsingleton (M : Type*) [AddCommGroup M] [Module A M] [Subsingleton M] :
    IsReflexive A M where
  bijective_dual_eval' := by
    refine ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun Φ ↦ ⟨0, ?_⟩⟩
    have : Subsingleton (Dual A M) := ⟨fun f g ↦ LinearMap.ext fun x ↦ by
      rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
    exact LinearMap.ext fun f ↦ by rw [Subsingleton.elim f 0, map_zero, map_zero]

/-- A finite product of reflexive modules is reflexive. -/
theorem IsReflexive.pi {ι : Type*} [Finite ι] (M : ι → Type*) [∀ i, AddCommGroup (M i)]
    [∀ i, Module A (M i)] [∀ i, IsReflexive A (M i)] : IsReflexive A (∀ i, M i) := by
  have := Fintype.ofFinite ι
  revert M
  refine Fintype.induction_empty_option (P := fun ι _ ↦ ∀ (M : ι → Type _)
    [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)] [∀ i, IsReflexive A (M i)],
      IsReflexive A (∀ i, M i)) ?_ ?_ ?_ ι
  · intro α β _ e h M _ _ _
    exact Module.equiv (LinearEquiv.piCongrLeft A M e)
  · intro M _ _ _
    exact IsReflexive.of_subsingleton _
  · intro α _ h M _ _ _
    have := h (fun i ↦ M (some i))
    exact Module.equiv (LinearEquiv.piOptionEquivProd A).symm

/-- **Reflexivity of a cyclic module.** Let `J` be an ideal of a commutative ring `A` and let
`K = (0 : J)` be its annihilator. If `J` is the annihilator of `K` (an `x` killing `K` lies in
`J`) and every `A`-linear map `K ⟶ A` is a multiplication, then `A ⧸ J` is reflexive: its dual
is `K`, through `φ ↦ φ 1`, and its double dual is then `A ⧸ J` again. -/
theorem isReflexive_quotient_of_colon (J : Ideal A)
    (h₁ : ∀ x : A, (∀ c ∈ (⊥ : Ideal A).colon (J : Set A), x * c = 0) → x ∈ J)
    (h₂ : ∀ f : (⊥ : Ideal A).colon (J : Set A) →ₗ[A] A, ∃ b : A, ∀ c, f c = b * c) :
    IsReflexive A (A ⧸ J) := by
  set K := (⊥ : Ideal A).colon (J : Set A)
  have hK (c : A) : c ∈ K ↔ ∀ j ∈ J, c * j = 0 := by
    simp only [K, Submodule.mem_colon, SetLike.mem_coe, smul_eq_mul, Submodule.mem_bot]
  -- the functional `x mod J ↦ x c` attached to `c ∈ K`
  let ψ (c : K) : Dual A (A ⧸ J) := J.liftQ (LinearMap.mulRight A (c : A)) fun j hj ↦ by
    simp only [LinearMap.mem_ker, LinearMap.mulRight_apply]
    rw [mul_comm]
    exact (hK c).1 c.2 j hj
  have hψ (c : K) (x : A) : ψ c (Submodule.Quotient.mk x) = x * c := rfl
  -- every functional is of this form, with `c = φ 1`
  have hφK (φ : Dual A (A ⧸ J)) : φ (Submodule.Quotient.mk 1) ∈ K := by
    refine (hK _).2 fun j hj ↦ ?_
    rw [mul_comm, ← smul_eq_mul, ← map_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one,
      (Submodule.Quotient.mk_eq_zero J).2 hj, map_zero]
  have hφ (φ : Dual A (A ⧸ J)) : φ = ψ ⟨_, hφK φ⟩ := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ ?_)
    change φ (Submodule.Quotient.mk x) = x * φ (Submodule.Quotient.mk 1)
    rw [← smul_eq_mul, ← map_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
  refine ⟨⟨fun q q' hqq' ↦ ?_, fun Φ ↦ ?_⟩⟩
  · rw [← sub_eq_zero, ← map_sub] at hqq'
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective J (q - q')
    rw [← sub_eq_zero, ← hx, Submodule.Quotient.mk_eq_zero]
    refine h₁ x fun c hc ↦ ?_
    have := LinearMap.congr_fun hqq' (ψ ⟨c, hc⟩)
    rwa [Dual.eval_apply, ← hx, hψ] at this
  · let f : K →ₗ[A] A :=
      { toFun c := Φ (ψ c)
        map_add' c c' := by
          rw [← map_add]
          congr 1
          exact Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ by
            change x * ((c + c' : K) : A) = x * c + x * c'
            simp [mul_add])
        map_smul' a c := by
          rw [RingHom.id_apply, ← map_smul]
          congr 1
          exact Submodule.linearMap_qext _ (LinearMap.ext fun x ↦ by
            change x * ((a • c : K) : A) = a * (x * c)
            simp [mul_left_comm]) }
    obtain ⟨b, hb⟩ := h₂ f
    refine ⟨Submodule.Quotient.mk b, LinearMap.ext fun φ ↦ ?_⟩
    rw [Dual.eval_apply, hφ φ, hψ]
    exact (hb _).symm

end Module
