import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Lemmas

/-! # Invariant anisotropic forms and sums of orthogonal complements -/

noncomputable section

open TensorProduct

namespace Langlands.LinearAlgebra.InvariantFormComplements

section Denominators

variable {M : Type*} [AddCommGroup M]

/-- Every element of `ℚ ⊗[ℤ] M` has a positive integral multiple of the form `1 ⊗ m`. -/
theorem exists_nsmul_eq_one_tmul (y : ℚ ⊗[ℤ] M) :
    ∃ n : ℕ, 0 < n ∧ ∃ m : M, (n : ℚ) • y = (1 : ℚ) ⊗ₜ[ℤ] m := by
  induction y using TensorProduct.inductionOn with
  | tmul q m =>
    refine ⟨q.den, q.den_pos, q.num • m, ?_⟩
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_comm, Rat.mul_den_eq_num,
      ← TensorProduct.smul_tmul, ← Int.cast_smul_eq_zsmul ℚ, smul_eq_mul, mul_one]
  | add y z hy hz =>
    obtain ⟨a, ha, m, hm⟩ := hy
    obtain ⟨b, hb, m', hm'⟩ := hz
    refine ⟨a * b, Nat.mul_pos ha hb, b • m + a • m', ?_⟩
    have hy' : ((a * b : ℕ) : ℚ) • y = (b : ℚ) • ((a : ℚ) • y) := by
      rw [smul_smul, Nat.cast_mul, mul_comm]
    have hz' : ((a * b : ℕ) : ℚ) • z = (a : ℚ) • ((b : ℚ) • z) := by
      rw [smul_smul, Nat.cast_mul]
    rw [smul_add, hy', hz', hm, hm', TensorProduct.tmul_add,
      Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← TensorProduct.tmul_smul,
      ← TensorProduct.tmul_smul]

end Denominators

section Complements

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]

omit [FiniteDimensional K E] in
/-- A vector orthogonal on the left to `S` lies in `V`, when `V ⊔ S = ⊤`, `V` is
left-orthogonal to `S`, and the form is anisotropic. -/
theorem mem_of_forall_apply_eq_zero (B : LinearMap.BilinForm K E)
    (hB : ∀ x, B x x = 0 → x = 0) {V S : Submodule K E} (h : V ⊔ S = ⊤)
    (hVS : ∀ v ∈ V, ∀ s ∈ S, B v s = 0) {z : E} (hz : ∀ s ∈ S, B z s = 0) : z ∈ V := by
  have hmem : z ∈ V ⊔ S := h ▸ Submodule.mem_top
  obtain ⟨v, hv, s, hs, rfl⟩ := Submodule.mem_sup.mp hmem
  have hss : B s s = 0 := by
    have h1 := hz s hs
    rw [map_add, LinearMap.add_apply, hVS v hv s hs, zero_add] at h1
    exact h1
  rw [hB s hss, add_zero]
  exact hv

/-- Under an anisotropic form, if `V₁ ⊕ S₁` and `V₂ ⊕ S₂` span, each `Vᵢ` is left-orthogonal
to `Sᵢ`, and `V` is left-orthogonal to a subspace containing `S₁ ⊓ S₂`, then
`V ≤ V₁ ⊔ V₂`. -/
theorem le_sup_of_anisotropic (B : LinearMap.BilinForm K E)
    (hB : ∀ x, B x x = 0 → x = 0)
    {V₁ S₁ V₂ S₂ V S : Submodule K E}
    (h₁ : V₁ ⊔ S₁ = ⊤) (h₂ : V₂ ⊔ S₂ = ⊤)
    (o₁ : ∀ v ∈ V₁, ∀ s ∈ S₁, B v s = 0) (o₂ : ∀ v ∈ V₂, ∀ s ∈ S₂, B v s = 0)
    (o : ∀ v ∈ V, ∀ s ∈ S, B v s = 0) (hS : S₁ ⊓ S₂ ≤ S) : V ≤ V₁ ⊔ V₂ := by
  have hinj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    exact hB x (by rw [LinearMap.mem_ker.mp hx, LinearMap.zero_apply])
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq).symm).mp hinj
  intro x hx
  have hmem : B x ∈ (S₁ ⊓ S₂).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    exact o x hx w (hS hw)
  rw [Subspace.dualAnnihilator_inf_eq] at hmem
  obtain ⟨f₁, hf₁, f₂, hf₂, hf⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨z₁, rfl⟩ := hsurj f₁
  obtain ⟨z₂, rfl⟩ := hsurj f₂
  have hz₁ : z₁ ∈ V₁ := mem_of_forall_apply_eq_zero B hB h₁ o₁
    ((Submodule.mem_dualAnnihilator _).mp hf₁)
  have hz₂ : z₂ ∈ V₂ := mem_of_forall_apply_eq_zero B hB h₂ o₂
    ((Submodule.mem_dualAnnihilator _).mp hf₂)
  have hx' : x = z₁ + z₂ := hinj (by rw [map_add, hf])
  rw [hx']
  exact Submodule.add_mem_sup hz₁ hz₂

end Complements

section Invariant

variable {E : Type*} [AddCommGroup E] [Module ℚ E]

/-- A form invariant under `s` pairs an `s`-fixed vector to zero with a vector negated by `s`. -/
theorem apply_eq_zero_of_fixed_of_neg (B : LinearMap.BilinForm ℚ E) (s : E →ₗ[ℚ] E)
    (hs : ∀ x y, B (s x) (s y) = B x y) {v a : E} (hv : s v = v) (ha : s a = -a) :
    B v a = 0 := by
  have h := hs v a
  rw [hv, ha, map_neg] at h
  linarith

variable [FiniteDimensional ℚ E]

/-- A finite group of linear automorphisms of a finite-dimensional rational vector space
preserves some anisotropic bilinear form. -/
theorem exists_invariant_anisotropic {W : Type*} [Group W] [Finite W]
    (ρ : W →* (E ≃ₗ[ℚ] E)) :
    ∃ B : LinearMap.BilinForm ℚ E, (∀ x, B x x = 0 → x = 0) ∧
      ∀ w x y, B (ρ w x) (ρ w y) = B x y := by
  let := Fintype.ofFinite W
  let b := Module.finBasis ℚ E
  let B₀ : LinearMap.BilinForm ℚ E :=
    ∑ i, (LinearMap.mul ℚ ℚ).compl₁₂ (b.coord i) (b.coord i)
  have hB₀ (x y : E) : B₀ x y = ∑ i, b.coord i x * b.coord i y := by
    simp [B₀, LinearMap.sum_apply]
  have hB₀nonneg (x : E) : 0 ≤ B₀ x x := by
    rw [hB₀]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hB₀zero (x : E) (hx : B₀ x x = 0) : x = 0 := by
    rw [hB₀] at hx
    have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg
      (b.coord i x)).mp hx
    apply b.ext_elem
    intro i
    simpa using hi i (Finset.mem_univ i)
  let B : LinearMap.BilinForm ℚ E :=
    ∑ w, B₀.compl₁₂ (ρ w).toLinearMap (ρ w).toLinearMap
  have hB (x y : E) : B x y = ∑ w, B₀ (ρ w x) (ρ w y) := by
    simp [B, LinearMap.sum_apply]
  refine ⟨B, fun x hx => ?_, fun g x y => ?_⟩
  · rw [hB] at hx
    have hw := (Finset.sum_eq_zero_iff_of_nonneg fun w _ => hB₀nonneg (ρ w x)).mp hx 1
      (Finset.mem_univ 1)
    rw [map_one] at hw
    exact hB₀zero x hw
  · rw [hB, hB]
    refine Fintype.sum_equiv (Equiv.mulRight g) _ _ fun w => ?_
    simp [map_mul, LinearEquiv.mul_apply]

end Invariant

end Langlands.LinearAlgebra.InvariantFormComplements
