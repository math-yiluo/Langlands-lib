import Langlands.GroupScheme.KostantRosenlicht.Points
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Rational-point and specialization tools for the Rosenlicht tensor-unit proof. -/

universe u v w

open scoped TensorProduct

noncomputable section

namespace Langlands.Algebra.Rosenlicht

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {A : Type v} [CommRing A] [Algebra k A] [Algebra.FiniteType k A]

/-- A maximal ideal is the kernel of a rational point. -/
theorem exists_point_with_kernel (m : Ideal A) [m.IsMaximal] :
    ∃ x : A →ₐ[k] k, RingHom.ker x = m :=
  Langlands.GroupScheme.KostantRosenlicht.exists_algHom_ker_eq (k := k) m

/-- Finite-type nonzero algebras over an algebraically closed field have points. -/
theorem exists_point [Nontrivial A] : Nonempty (A →ₐ[k] k) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let := hm
  obtain ⟨x, _⟩ := exists_point_with_kernel (k := k) m
  exact ⟨x⟩

/-- Rational points detect zero in a finite-type domain. -/
theorem eq_zero_of_all_points [IsDomain A] (a : A)
    (ha : ∀ x : A →ₐ[k] k, x a = 0) : a = 0 := by
  let : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  have h : a ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    intro m hm
    obtain ⟨_, hm⟩ := hm
    let := hm
    obtain ⟨x, hx⟩ := exists_point_with_kernel (k := k) m
    rw [← hx]
    exact ha x
  rw [← Ideal.radical_eq_jacobson,
    Ideal.IsPrime.radical (inferInstance : (⊥ : Ideal A).IsPrime)] at h
  exact h

variable {B : Type w} [CommRing B] [Algebra k B]

/-- Evaluation of the first tensor factor at a rational point. -/
def specialize (x : A →ₐ[k] k) : A ⊗[k] B →ₐ[k] B :=
  (Algebra.TensorProduct.lid k B).toAlgHom.comp
    (Algebra.TensorProduct.map x (AlgHom.id k B))

omit [IsAlgClosed k] [Algebra.FiniteType k A] in
@[simp]
theorem specialize_tmul (x : A →ₐ[k] k) (a : A) (b : B) :
    specialize x (a ⊗ₜ[k] b) = x a • b := by
  simp [specialize]

/-- Contract the second tensor factor against a linear form. -/
def contract (f : B →ₗ[k] k) : A ⊗[k] B →ₗ[k] A :=
  (TensorProduct.rid k A).toLinearMap.comp (f.lTensor A)

omit [IsAlgClosed k] [Algebra.FiniteType k A] in
@[simp]
theorem contract_tmul (f : B →ₗ[k] k) (a : A) (b : B) :
    contract f (a ⊗ₜ[k] b) = f b • a := by
  simp [contract]

omit [IsAlgClosed k] [Algebra.FiniteType k A] in
theorem contract_specialize (f : B →ₗ[k] k) (x : A →ₐ[k] k)
    (t : A ⊗[k] B) : x (contract f t) = f (specialize x t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
      rw [contract_tmul, specialize_tmul, map_smul, map_smul]
      exact mul_comm _ _
  | add t t' ht ht' => simp [ht, ht']

omit [IsAlgClosed k] [Algebra.FiniteType k A] in
/-- The linear forms on the second factor jointly detect a tensor. -/
theorem tensor_eq_zero_of_contract (t : A ⊗[k] B)
    (ht : ∀ f : B →ₗ[k] k, contract f t = 0) : t = 0 := by
  let b := Module.Free.chooseBasis k B
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i
  rw [map_zero, Finsupp.zero_apply, TensorProduct.equivFinsuppOfBasisRight_apply]
  exact ht (b.coord i)

/-- Specializing at all rational points detects a tensor. -/
theorem tensor_eq_zero_of_specialize [IsDomain A] (t : A ⊗[k] B)
    (ht : ∀ x : A →ₐ[k] k, specialize x t = 0) : t = 0 := by
  apply tensor_eq_zero_of_contract
  intro f
  apply eq_zero_of_all_points (k := k)
  intro x
  rw [contract_specialize, ht, map_zero]

/-- A finite-valued tensor family over a domain is constant. -/
theorem constant_of_finite_specializations [IsDomain A] (t : A ⊗[k] B)
    (hfinite : (Set.range (fun x : A →ₐ[k] k => specialize x t)).Finite) :
    ∃ b : B, t = (1 : A) ⊗ₜ[k] b := by
  classical
  let S := Set.range (fun x : A →ₐ[k] k => specialize x t)
  let : Fintype S := hfinite.fintype
  by_contra h
  have hw (b : S) : ∃ f : B →ₗ[k] k, contract f (t - (1 : A) ⊗ₜ[k] (b : B)) ≠ 0 := by
    by_contra hb
    push Not at hb
    have hz := tensor_eq_zero_of_contract (t - (1 : A) ⊗ₜ[k] (b : B)) hb
    exact h ⟨b, sub_eq_zero.mp hz⟩
  choose f hf using hw
  let c : S → A := fun b => contract (f b) (t - (1 : A) ⊗ₜ[k] (b : B))
  have hc : (∏ b : S, c b) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun b _ => hf b)
  apply hc
  apply eq_zero_of_all_points (k := k)
  intro x
  rw [map_prod]
  let b : S := ⟨specialize x t, ⟨x, rfl⟩⟩
  apply Finset.prod_eq_zero (Finset.mem_univ b)
  change x (contract (f b) (t - (1 : A) ⊗ₜ[k] (b : B))) = 0
  rw [contract_specialize]
  simp [b]

omit [IsAlgClosed k] [Algebra.FiniteType k A] in
/-- A tensor family's values lie in a finite-dimensional subspace of the second factor. -/
theorem exists_finite_specialization_space (t : A ⊗[k] B) :
    ∃ V : Submodule k B, V.FG ∧ ∀ x : A →ₐ[k] k, specialize x t ∈ V := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
      refine ⟨Submodule.span k {b}, Submodule.fg_span_singleton b, ?_⟩
      intro x
      rw [specialize_tmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton b))
  | add t t' ht ht' =>
      obtain ⟨V, hV, ht⟩ := ht
      obtain ⟨W, hW, ht'⟩ := ht'
      refine ⟨V ⊔ W, hV.sup hW, ?_⟩
      intro x
      rw [map_add]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (ht x))
        (Submodule.mem_sup_right (ht' x))

/-- Evaluation of the second tensor factor at a rational point. -/
def evaluateRight (epsilon : B →ₐ[k] k) : A ⊗[k] B →ₐ[k] A :=
  (Algebra.TensorProduct.rid k k A).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id k A) epsilon)

omit [IsAlgClosed k] [Algebra.FiniteType k A] in
@[simp]
theorem evaluateRight_tmul (epsilon : B →ₐ[k] k) (a : A) (b : B) :
    evaluateRight epsilon (a ⊗ₜ[k] b) = epsilon b • a := by
  simp [evaluateRight]

omit [IsAlgClosed k] [Algebra.FiniteType k A] in
/-- The two scalar specializations commute. -/
theorem specialize_evaluateRight (epsilon : B →ₐ[k] k) (x : A →ₐ[k] k)
    (t : A ⊗[k] B) : epsilon (specialize x t) = x (evaluateRight epsilon t) := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
      rw [specialize_tmul, evaluateRight_tmul, map_smul, map_smul]
      exact mul_comm _ _
  | add t t' ht ht' => simp [ht, ht']

end Langlands.Algebra.Rosenlicht
