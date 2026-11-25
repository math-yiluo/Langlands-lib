/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Central.TensorProduct
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Base change of central simple algebras

Let `A` be a central simple algebra over a field `K` and `F` a field extension of `K`. Then
`F ⊗[K] A` is a central simple algebra over `F`.

## Main statements

- `Algebra.IsCentral.baseChange`: `F ⊗[K] A` is central over `F`.
- `IsSimpleRing.tensorProduct_of_isCentral`: `F ⊗[K] A` is simple.

## Implementation notes

Both proofs write an element of `F ⊗[K] A` in coordinates `∑ fⱼ ⊗ aⱼ` with respect to a
`K`-basis `(fⱼ)` of `F`, and use that commutators with `1 ⊗ a` act coordinatewise.
-/

@[expose] public section

open TensorProduct

namespace Algebra.TensorProduct

variable {K F A ι : Type*} [CommRing K] [Ring F] [Algebra K F] [Ring A] [Algebra K A]
  [DecidableEq ι]

/-- Left multiplication by `1 ⊗ a` acts on the coordinates `x = ∑ bⱼ ⊗ aⱼ` with respect to
a basis `b` by left multiplication by `a`. -/
lemma equivFinsuppOfBasisLeft_one_tmul_mul (b : Module.Basis ι K F) (a : A) (x : F ⊗[K] A)
    (j : ι) : equivFinsuppOfBasisLeft b ((1 ⊗ₜ a) * x) j = a * equivFinsuppOfBasisLeft b x j := by
  induction x using TensorProduct.inductionOn with
  | tmul f a' => simp
  | add x y hx hy => simp [mul_add, hx, hy]

/-- Right multiplication by `1 ⊗ a` acts on the coordinates `x = ∑ bⱼ ⊗ aⱼ` with respect to
a basis `b` by right multiplication by `a`. -/
lemma equivFinsuppOfBasisLeft_mul_one_tmul (b : Module.Basis ι K F) (a : A) (x : F ⊗[K] A)
    (j : ι) : equivFinsuppOfBasisLeft b (x * (1 ⊗ₜ a)) j = equivFinsuppOfBasisLeft b x j * a := by
  induction x using TensorProduct.inductionOn with
  | tmul f a' => simp
  | add x y hx hy => simp [add_mul, hx, hy]

end Algebra.TensorProduct

namespace Algebra.TensorProduct

/-- An element of `F ⊗[K] A` commuting with every `1 ⊗ a` lies in the image of `F`, provided
`A` is central over `K` and `F` is free over `K`. -/
lemma mem_bot_of_forall_commute_one_tmul {K F A : Type*} [CommRing K] [CommRing F]
    [Algebra K F] [Module.Free K F] [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    (x : F ⊗[K] A) (hx : ∀ a : A, (1 ⊗ₜ a) * x = x * (1 ⊗ₜ a)) :
    x ∈ (⊥ : Subalgebra F (F ⊗[K] A)) := by
  classical
  let b := Module.Free.chooseBasis K F
  rw [← (equivFinsuppOfBasisLeft b).symm_apply_apply x, equivFinsuppOfBasisLeft_symm_apply]
  refine Subalgebra.sum_mem _ fun j _ ↦ ?_
  have hc : equivFinsuppOfBasisLeft b x j ∈ Subalgebra.center K A := by
    rw [Subalgebra.mem_center_iff]
    intro a
    rw [← equivFinsuppOfBasisLeft_one_tmul_mul, hx, equivFinsuppOfBasisLeft_mul_one_tmul]
  obtain ⟨c, hc⟩ := Algebra.mem_bot.mp (Algebra.IsCentral.out hc)
  dsimp only
  rw [← hc, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
  exact Subalgebra.algebraMap_mem _ (c • b j)

end Algebra.TensorProduct

namespace Algebra.TensorProduct

/-- A nonzero two-sided ideal of `F ⊗[K] A`, where `A` is a central simple `K`-algebra and `F`
is a free `K`-algebra, contains a nonzero element of the image of `F`. -/
lemma exists_ne_zero_mem_bot_of_ne_bot {K F A : Type*} [CommRing K] [CommRing F]
    [Algebra K F] [Module.Free K F] [Ring A] [Algebra K A] [Algebra.IsCentral K A]
    [IsSimpleRing A] (I : TwoSidedIdeal (F ⊗[K] A)) (hI : I ≠ ⊥) :
    ∃ x ∈ I, x ≠ 0 ∧ x ∈ (⊥ : Subalgebra F (F ⊗[K] A)) := by
  classical
  let e := equivFinsuppOfBasisLeft (Module.Free.chooseBasis K F) (N := A)
  have hex : ∃ n, ∃ x ∈ I, x ≠ 0 ∧ (e x).support.card = n := by
    by_contra! h
    refine hI (eq_bot_iff.mpr fun x hx ↦ ?_)
    rw [TwoSidedIdeal.mem_bot]
    by_contra hx0
    exact h _ x hx hx0 rfl
  obtain ⟨x, hxI, hx0, hxn⟩ := Nat.find_spec hex
  obtain ⟨j₀, hj₀⟩ := Finsupp.ne_iff.mp ((map_ne_zero_iff e e.injective).mpr hx0)
  let J : TwoSidedIdeal A := .mk' {y | ∃ z ∈ I, (∀ j, e x j = 0 → e z j = 0) ∧ e z j₀ = y}
    ⟨0, I.zero_mem, by simp, by simp⟩
    (fun ⟨z, hz, hzs, hzj⟩ ⟨z', hz', hzs', hzj'⟩ ↦ ⟨z + z', I.add_mem hz hz',
      fun j hj ↦ by simp [hzs j hj, hzs' j hj], by simp [hzj, hzj']⟩)
    (fun ⟨z, hz, hzs, hzj⟩ ↦ ⟨-z, I.neg_mem hz, fun j hj ↦ by simp [hzs j hj], by simp [hzj]⟩)
    (fun {a} _ ⟨z, hz, hzs, hzj⟩ ↦ ⟨(1 ⊗ₜ a) * z, I.mul_mem_left _ _ hz,
      fun j hj ↦ by rw [equivFinsuppOfBasisLeft_one_tmul_mul, hzs j hj, mul_zero],
      by rw [equivFinsuppOfBasisLeft_one_tmul_mul, hzj]⟩)
    (fun {_ a} ⟨z, hz, hzs, hzj⟩ ↦ ⟨z * (1 ⊗ₜ a), I.mul_mem_right _ _ hz,
      fun j hj ↦ by rw [equivFinsuppOfBasisLeft_mul_one_tmul, hzs j hj, zero_mul],
      by rw [equivFinsuppOfBasisLeft_mul_one_tmul, hzj]⟩)
  have h1 : (1 : A) ∈ J := IsSimpleRing.one_mem_of_ne_zero_mem J hj₀
    ((TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _).mpr ⟨x, hxI, fun _ h ↦ h, rfl⟩)
  obtain ⟨z, hzI, hzs, hz1⟩ := (TwoSidedIdeal.mem_mk' _ _ _ _ _ _ _).mp h1
  refine ⟨z, hzI, ?_, mem_bot_of_forall_commute_one_tmul z fun a ↦ ?_⟩
  · rintro rfl
    simp at hz1
  by_contra hne
  have hy (j) : e ((1 ⊗ₜ a) * z - z * (1 ⊗ₜ a)) j = a * e z j - e z j * a := by
    rw [map_sub, Finsupp.sub_apply, equivFinsuppOfBasisLeft_one_tmul_mul,
      equivFinsuppOfBasisLeft_mul_one_tmul]
  have hsub : (e ((1 ⊗ₜ a) * z - z * (1 ⊗ₜ a))).support ⊆ (e x).support.erase j₀ := by
    intro j hj
    rw [Finsupp.mem_support_iff, hy] at hj
    rw [Finset.mem_erase, Finsupp.mem_support_iff]
    refine ⟨?_, fun h ↦ hj ?_⟩
    · rintro rfl
      simp [hz1] at hj
    · simp [hzs j h]
  refine Nat.find_min hex ?_ ⟨_, I.sub_mem (I.mul_mem_left _ _ hzI) (I.mul_mem_right _ _ hzI),
    sub_ne_zero.mpr hne, rfl⟩
  rw [← hxn]
  exact (Finset.card_le_card hsub).trans_lt
    (Finset.card_erase_lt_of_mem (Finsupp.mem_support_iff.mpr hj₀))

end Algebra.TensorProduct

variable (K F A : Type*) [Field K] [Field F] [Algebra K F] [Ring A] [Algebra K A]

/-- The base change `F ⊗[K] A` of a central `K`-algebra `A` to a field extension `F` is
central over `F`. -/
instance Algebra.IsCentral.baseChange [Algebra.IsCentral K A] :
    Algebra.IsCentral F (F ⊗[K] A) where
  out x hx := Algebra.TensorProduct.mem_bot_of_forall_commute_one_tmul x fun _ ↦
    Subalgebra.mem_center_iff.mp hx _

/-- The base change `F ⊗[K] A` of a central simple `K`-algebra `A` to a field extension `F`
is simple. -/
instance IsSimpleRing.tensorProduct_of_isCentral [Algebra.IsCentral K A] [IsSimpleRing A] :
    IsSimpleRing (F ⊗[K] A) := by
  have : Nontrivial (F ⊗[K] A) := (Algebra.TensorProduct.includeLeft_injective (S := K)
    (FaithfulSMul.algebraMap_injective K A)).nontrivial
  refine IsSimpleRing.of_eq_bot_or_eq_top fun I ↦ or_iff_not_imp_left.mpr fun hI ↦ ?_
  obtain ⟨x, hxI, hx0, hx⟩ := Algebra.TensorProduct.exists_ne_zero_mem_bot_of_ne_bot I hI
  obtain ⟨f, rfl⟩ := Algebra.mem_bot.mp hx
  refine I.eq_top ?_
  have hf : f ≠ 0 := by
    rintro rfl
    exact hx0 (map_zero _)
  simpa [← map_mul, inv_mul_cancel₀ hf, Algebra.TensorProduct.one_def] using
    I.mul_mem_left (algebraMap F _ f⁻¹) _ hxI
