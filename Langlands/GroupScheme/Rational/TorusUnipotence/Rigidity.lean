import Langlands.GroupScheme.Rational.TorusUnipotence.BigCellStatement
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Algebra.DirectSum.Module

/-! # Degree-zero rigidity from big-cell injectivity -/

noncomputable section

universe u

open TensorProduct

namespace Langlands.GroupScheme.TorusUnipotence

section Separation

variable {k : Type*} [Field k] {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W]
  [Module k W]

/-- The coordinates of a tensor with respect to a basis of its second factor are the
contractions with the coordinate functionals. -/
theorem equivFinsuppOfBasisRight_apply {ι : Type*} [DecidableEq ι] (𝒷 : Module.Basis ι k W)
    (t : V ⊗[k] W) (i : ι) :
    TensorProduct.equivFinsuppOfBasisRight 𝒷 t i =
      TensorProduct.rid k V ((𝒷.coord i).lTensor V t) := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    rw [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, LinearMap.lTensor_tmul,
      TensorProduct.rid_tmul, Module.Basis.coord_apply]
  | add t₁ t₂ h₁ h₂ => rw [map_add, Finsupp.add_apply, h₁, h₂, map_add, map_add]

/-- Over a field, a tensor killed by every functional on its second factor is zero. -/
theorem eq_zero_of_forall_lTensor {t : V ⊗[k] W}
    (h : ∀ m : Module.Dual k W, TensorProduct.rid k V (m.lTensor V t) = 0) : t = 0 := by
  classical
  let 𝒷 := Module.Free.chooseBasis k W
  apply (TensorProduct.equivFinsuppOfBasisRight 𝒷).injective
  ext i
  rw [equivFinsuppOfBasisRight_apply, h, map_zero, Finsupp.zero_apply]

end Separation

section Projection

variable {k : Type*} [CommRing k] {A : Type*} [AddCommGroup A] [Module k A]
  (𝒜 : ℤ → Submodule k A) [DirectSum.Decomposition 𝒜]

/-- The projection onto the sum of the positive-degree components. -/
def posProj : A →ₗ[k] A :=
  DirectSum.toModule k ℤ A (fun d => if 0 < d then (𝒜 d).subtype else 0) ∘ₗ
    (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap

theorem posProj_of_mem {d : ℤ} {b : A} (hb : b ∈ 𝒜 d) :
    posProj 𝒜 b = if 0 < d then b else 0 := by
  rw [posProj, LinearMap.comp_apply, LinearEquiv.coe_coe, DirectSum.decomposeLinearEquiv_apply,
    DirectSum.decompose_of_mem 𝒜 hb, ← DirectSum.lof_eq_of k, DirectSum.toModule_lof]
  split_ifs <;> simp

end Projection

section Rigidity

variable {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] (ε : A →ₐ[k] k)

theorem sub_algebraMap_mem_graded_zero {a : A} (ha : a ∈ 𝒜 0) :
    a - algebraMap k A (ε a) ∈ 𝒜 0 ∧ ε (a - algebraMap k A (ε a)) = 0 :=
  ⟨Submodule.sub_mem _ ha (SetLike.algebraMap_mem_graded 𝒜 _), by
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]⟩

/-- On degree zero, the positive big-cell quotient is the augmentation. -/
theorem mk_plusIdeal_of_mem_zero {a : A} (ha : a ∈ 𝒜 0) :
    Ideal.Quotient.mk (plusIdeal 𝒜 ε) a = algebraMap k _ (ε a) := by
  rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq]
  exact Ideal.subset_span (Or.inr (sub_algebraMap_mem_graded_zero 𝒜 ε ha))

/-- On degree zero, the negative big-cell quotient is the augmentation. -/
theorem mk_minusIdeal_of_mem_zero {a : A} (ha : a ∈ 𝒜 0) :
    Ideal.Quotient.mk (minusIdeal 𝒜 ε) a = algebraMap k _ (ε a) := by
  rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq]
  exact Ideal.subset_span (Or.inr (sub_algebraMap_mem_graded_zero 𝒜 ε ha))

variable {𝒜 ε}

/-- After discarding the positive-degree part, the positive big-cell quotient is the
augmentation. -/
theorem mk_plusIdeal_sub_posProj (hε : ∀ d : ℤ, d ≠ 0 → ∀ a ∈ 𝒜 d, ε a = 0) (x : A) :
    Ideal.Quotient.mk (plusIdeal 𝒜 ε) (x - posProj 𝒜 x) = algebraMap k _ (ε x) := by
  induction x using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous m =>
    obtain ⟨b, hb⟩ := m
    rename_i d
    change Ideal.Quotient.mk _ (b - posProj 𝒜 b) = algebraMap k _ (ε b)
    rw [posProj_of_mem 𝒜 hb]
    rcases lt_trichotomy d 0 with hd | rfl | hd
    · rw [ite_eq_right (not_lt.2 hd.le), sub_zero, hε d hd.ne b hb, map_zero,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (Or.inl ⟨d, hd, hb⟩)
    · rw [ite_eq_right (lt_irrefl 0), sub_zero]
      exact mk_plusIdeal_of_mem_zero 𝒜 ε hb
    · rw [ite_eq_left hd, sub_self, map_zero, hε d hd.ne' b hb, map_zero]
  | add x y hx hy =>
    rw [map_add, add_sub_add_comm, map_add, hx, hy, map_add, map_add]

/-- The big-cell map on a tensor whose second factor has no positive-degree part. -/
theorem map_quotient_lTensor_sub_posProj (hε : ∀ d : ℤ, d ≠ 0 → ∀ a ∈ 𝒜 d, ε a = 0)
    (t : A ⊗[k] A) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (minusIdeal 𝒜 ε))
        (Ideal.Quotient.mkₐ k (plusIdeal 𝒜 ε))
        ((LinearMap.id - posProj 𝒜).lTensor A t) =
      Ideal.Quotient.mk (minusIdeal 𝒜 ε)
        (Algebra.TensorProduct.rid k k A (Algebra.TensorProduct.map (AlgHom.id k A) ε t)) ⊗ₜ 1 := by
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    rw [LinearMap.lTensor_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.rid_tmul, AlgHom.id_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.mkₐ_eq_mk, LinearMap.sub_apply, LinearMap.id_apply,
      mk_plusIdeal_sub_posProj hε, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
    congr 1
  | add t₁ t₂ h₁ h₂ =>
    rw [map_add, map_add, h₁, h₂, map_add, map_add, map_add, TensorProduct.add_tmul]

/-- **Degree-zero rigidity.** If the big-cell map is injective, a degree-zero element whose
comultiplication is killed by every functional vanishing in nonpositive degrees on the second
factor is a scalar. -/
theorem eq_algebraMap_of_lTensor_eq_zero {Δ : A →ₐ[k] A ⊗[k] A}
    (hinj : Function.Injective (bigCellMap 𝒜 ε Δ))
    (hε : ∀ d : ℤ, d ≠ 0 → ∀ a ∈ 𝒜 d, ε a = 0)
    (hr : ∀ x, Algebra.TensorProduct.rid k k A
      (Algebra.TensorProduct.map (AlgHom.id k A) ε (Δ x)) = x)
    {a : A} (ha : a ∈ 𝒜 0)
    (hm : ∀ m : Module.Dual k A, (∀ d : ℤ, d ≤ 0 → ∀ b ∈ 𝒜 d, m b = 0) →
      TensorProduct.rid k A (m.lTensor A (Δ a)) = 0) :
    a = algebraMap k A (ε a) := by
  have hP : (posProj 𝒜).lTensor A (Δ a) = 0 := by
    refine eq_zero_of_forall_lTensor fun m => ?_
    have := hm (m ∘ₗ posProj 𝒜) fun d hd b hb => by
      rw [LinearMap.comp_apply, posProj_of_mem 𝒜 hb, ite_eq_right (not_lt.2 hd), map_zero]
    rwa [LinearMap.lTensor_comp_apply] at this
  have hQ : (LinearMap.id - posProj 𝒜).lTensor A (Δ a) = Δ a := by
    rw [LinearMap.lTensor_sub, LinearMap.sub_apply, LinearMap.lTensor_id, LinearMap.id_apply, hP,
      sub_zero]
  apply hinj
  rw [AlgHom.commutes, bigCellMap, AlgHom.comp_apply, ← hQ, map_quotient_lTensor_sub_posProj hε,
    hr a, mk_minusIdeal_of_mem_zero 𝒜 ε ha, Algebra.TensorProduct.algebraMap_apply]

end Rigidity

end Langlands.GroupScheme.TorusUnipotence
