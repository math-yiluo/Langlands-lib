import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Algebra

/-! # Pointed Laurent functions and their nonconstant coefficients -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.LaurentAugmentation

open AddMonoidAlgebra

variable (k : Type u) [CommRing k] (M : Type v) [AddCommMonoid M]

/-- Evaluation at the identity of the diagonalizable group with character monoid `M`. -/
def augmentation : AddMonoidAlgebra k M →ₐ[k] k :=
  Bialgebra.counitAlgHom k (AddMonoidAlgebra k M)

/-- Laurent functions vanishing at the identity, considered as a vector space. -/
def space : Submodule k (AddMonoidAlgebra k M) :=
  LinearMap.ker (augmentation k M).toLinearMap

/-- The pointed monomial `X^m - 1`. -/
def delta (m : M) : AddMonoidAlgebra k M :=
  single m 1 - 1

variable {k M}

@[simp] theorem augmentation_single (m : M) (a : k) :
    augmentation k M (single m a) = a := by
  simp [augmentation]

@[simp] theorem augmentation_delta (m : M) :
    augmentation k M (delta k M m) = 0 := by
  simp [delta]

@[simp] theorem mem_space (f : AddMonoidAlgebra k M) :
    f ∈ space k M ↔ augmentation k M f = 0 := Iff.rfl

@[simp] theorem delta_zero : delta k M (0 : M) = 0 := by
  simp [delta, ← one_def]

open Classical in
theorem coeff_delta (m : M) (n : M) (hn : n ≠ 0) :
    (delta k M m).coeff n = if m = n then 1 else 0 := by
  simp [delta, coeff_sub, coeff_single, Finsupp.single_apply, one_def, hn]

/-- The nonconstant coefficients of a Laurent function. -/
def coefficients : AddMonoidAlgebra k M →ₗ[k] ({m : M // m ≠ 0} →₀ k) :=
  (Finsupp.lsubtypeDomain {m : M | m ≠ 0}).comp
    (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap

@[simp] theorem coefficients_apply (f : AddMonoidAlgebra k M) (m : {m : M // m ≠ 0}) :
    coefficients f m = f.coeff m := rfl

/-- Reconstruct a pointed Laurent function from its nonconstant coefficients. -/
def fromCoefficients : ({m : M // m ≠ 0} →₀ k) →ₗ[k] AddMonoidAlgebra k M :=
  Finsupp.linearCombination k (fun m => delta k M m.val)

@[simp] theorem fromCoefficients_single (m : {m : M // m ≠ 0}) (a : k) :
    fromCoefficients (Finsupp.single m a) = a • delta k M m.val := by
  simp [fromCoefficients]

theorem augmentation_fromCoefficients (c : {m : M // m ≠ 0} →₀ k) :
    augmentation k M (fromCoefficients c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd]
  | single m a => simp

@[simp] theorem coefficients_delta (m : {m : M // m ≠ 0}) :
    coefficients (delta k M m.val) = Finsupp.single m 1 := by
  classical
  ext n
  rw [coefficients_apply, coeff_delta _ _ n.property, Finsupp.single_apply]
  simp only [Subtype.ext_iff]

@[simp] theorem coefficients_fromCoefficients (c : {m : M // m ≠ 0} →₀ k) :
    coefficients (fromCoefficients c) = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd]
  | single m a =>
      rw [fromCoefficients_single, map_smul, coefficients_delta,
        Finsupp.smul_single_one]

theorem eq_zero_of_coefficients_eq_zero {f : AddMonoidAlgebra k M}
    (hf : augmentation k M f = 0) (hc : coefficients f = 0) : f = 0 := by
  classical
  have hsingle : f = single 0 (f.coeff 0) := by
    ext m
    by_cases hm : m = 0
    · subst m
      simp
    · have h := congrArg (fun c : {m : M // m ≠ 0} →₀ k => c ⟨m, hm⟩) hc
      simpa [coeff_single, hm, Ne.symm hm] using h
  have h0 : f.coeff 0 = 0 := by
    have h := congrArg (augmentation k M) hsingle
    rwa [hf, augmentation_single, eq_comm] at h
  rw [hsingle, h0, single_zero]

theorem fromCoefficients_coefficients {f : AddMonoidAlgebra k M}
    (hf : augmentation k M f = 0) :
    fromCoefficients (coefficients f) = f := by
  apply sub_eq_zero.mp
  apply eq_zero_of_coefficients_eq_zero
  · simp [augmentation_fromCoefficients, hf]
  · simp

/-- The augmentation ideal has coordinates indexed by the nonzero characters. -/
def equivalence : space k M ≃ₗ[k] ({m : M // m ≠ 0} →₀ k) :=
  LinearEquiv.ofBijective ((coefficients (k := k) (M := M)).comp (space k M).subtype) (by
    constructor
    · intro f g h
      apply Subtype.ext
      apply sub_eq_zero.mp
      apply eq_zero_of_coefficients_eq_zero
      · rw [map_sub, (mem_space _).mp f.property, (mem_space _).mp g.property, sub_self]
      · change coefficients f.val = coefficients g.val at h
        simpa using sub_eq_zero.mpr h
    · intro c
      exact ⟨⟨fromCoefficients c, augmentation_fromCoefficients c⟩,
        coefficients_fromCoefficients c⟩)

@[simp] theorem equivalence_apply (f : space k M) :
    equivalence f = coefficients f.val := rfl

@[simp] theorem equivalence_symm_apply (c : {m : M // m ≠ 0} →₀ k) :
    ((equivalence (k := k) (M := M)).symm c).val = fromCoefficients c := by
  have h : (equivalence (k := k) (M := M)).symm c =
      ⟨fromCoefficients c, augmentation_fromCoefficients c⟩ := by
    apply (equivalence (k := k) (M := M)).injective
    simp
  exact congrArg Subtype.val h

/-- The basis of pointed monomials, with the constant character omitted. -/
def basis : Module.Basis {m : M // m ≠ 0} k (space k M) :=
  Module.Basis.ofRepr (equivalence (k := k) (M := M))

@[simp] theorem basis_apply (m : {m : M // m ≠ 0}) :
    ((basis (k := k) (M := M)) m).val = delta k M m.val := by
  change ((equivalence (k := k) (M := M)).symm (Finsupp.single m 1)).val = _
  simp

section Frobenius

variable (p : ℕ) [Fact p.Prime] [CharP k p]

theorem delta_pow (m : M) (r : ℕ) :
    delta k M m ^ p ^ r = delta k M ((p ^ r) • m) := by
  have : CharP (AddMonoidAlgebra k M) p :=
    charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective k _) p
  simp [delta, sub_pow_char_pow, single_pow]

omit [CharP k p] in
theorem pow_mem_space {f : AddMonoidAlgebra k M} (hf : f ∈ space k M) (r : ℕ) :
    f ^ p ^ r ∈ space k M := by
  rw [mem_space, map_pow, (mem_space f).mp hf]
  exact zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)

end Frobenius

end Langlands.GroupScheme.LaurentAugmentation
