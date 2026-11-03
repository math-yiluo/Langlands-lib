import Langlands.Algebra.GradedHopf.TensorGrading
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Bialgebra.Primitive

/-! # Graded bialgebras -/

noncomputable section

open TensorProduct DirectSum Coalgebra

namespace Langlands.Algebra.GradedHopf

variable {ι k A : Type*} [DecidableEq ι] [AddCommGroup ι] [CommRing k] [CommRing A]

section GradedAlgebra

variable [Algebra k A] (𝒜 : ι → Submodule k A) [GradedAlgebra 𝒜]

theorem one_mem_zero : (1 : A) ∈ 𝒜 0 := SetLike.GradedOne.one_mem

theorem algebraMap_mem_zero (c : k) : algebraMap k A c ∈ 𝒜 0 := SetLike.algebraMap_mem_graded 𝒜 c

theorem gradeProj_mul_of_left_mem {i : ι} {a : A} (ha : a ∈ 𝒜 i) (n : ι) (b : A) :
    gradeProj 𝒜 n (a * b) = a * gradeProj 𝒜 (n - i) b := by
  rw [gradeProj_apply, gradeProj_apply, ← coe_decompose_mul_add_of_left_mem 𝒜 ha,
    add_sub_cancel]

theorem gradeProj_mul_of_right_mem {j : ι} {b : A} (hb : b ∈ 𝒜 j) (n : ι) (a : A) :
    gradeProj 𝒜 n (a * b) = gradeProj 𝒜 (n - j) a * b := by
  rw [mul_comm, gradeProj_mul_of_left_mem 𝒜 hb, mul_comm]

theorem gradeProj_algebraMap (n : ι) (c : k) :
    gradeProj 𝒜 n (algebraMap k A c) = if n = 0 then algebraMap k A c else 0 := by
  rw [gradeProj_of_mem 𝒜 (algebraMap_mem_zero 𝒜 c)]
  simp [eq_comm]

/-- An ideal is homogeneous as soon as all its elements have their components in it. -/
theorem gradeProj_mem_of_isHomogeneous {J : Ideal A} (hJ : J.IsHomogeneous 𝒜) (n : ι) {a : A}
    (ha : a ∈ J) : gradeProj 𝒜 n a ∈ J :=
  hJ n ha

end GradedAlgebra

section Bialgebra

variable [Bialgebra k A] (𝒜 : ι → Submodule k A) [GradedAlgebra 𝒜]

/-- A grading of a commutative bialgebra is compatible with the bialgebra structure: the
comultiplication carries degree `n` into the total-degree-`n` part of `A ⊗ A`, and the counit
vanishes in nonzero degrees. -/
structure IsGradedBialgebra : Prop where
  comul_mem : ∀ n, ∀ a ∈ 𝒜 n, comul (R := k) a ∈ tensorGrade 𝒜 𝒜 n
  counit_eq_zero : ∀ n ≠ 0, ∀ a ∈ 𝒜 n, counit (R := k) a = 0

variable {𝒜}

namespace IsGradedBialgebra

variable (h𝒜 : IsGradedBialgebra 𝒜)
include h𝒜

theorem comul_comp_gradeProj (n : ι) :
    comul (R := k) (A := A) ∘ₗ gradeProj 𝒜 n = tensorProj 𝒜 𝒜 n ∘ₗ comul (R := k) := by
  refine decompose_lhom_ext 𝒜 fun j => LinearMap.ext fun a => ?_
  simp only [LinearMap.comp_apply, Submodule.coe_subtype]
  rw [gradeProj_of_mem 𝒜 a.2, tensorProj_of_mem_tensorGrade 𝒜 𝒜 (h𝒜.comul_mem j a a.2)]
  split_ifs <;> simp

theorem comul_gradeProj (n : ι) (a : A) :
    comul (R := k) (gradeProj 𝒜 n a) = tensorProj 𝒜 𝒜 n (comul (R := k) a) :=
  LinearMap.congr_fun (h𝒜.comul_comp_gradeProj n) a

theorem counit_gradeProj (n : ι) (a : A) :
    counit (R := k) (gradeProj 𝒜 n a) = if n = 0 then counit (R := k) a else 0 := by
  induction a using Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i a =>
    rw [gradeProj_of_mem 𝒜 a.2]
    by_cases hi : i = 0
    · subst hi
      split_ifs <;> simp_all
    · have h0 := h𝒜.counit_eq_zero i hi a a.2
      split_ifs <;> simp_all
  | add a b ha hb => simp only [map_add, ha, hb]; split_ifs <;> simp

theorem counit_gradeProj_zero (a : A) : counit (R := k) (gradeProj 𝒜 0 a) = counit (R := k) a :=
  by rw [h𝒜.counit_gradeProj]; simp

theorem counit_gradeProj_ne (a : A) {n : ι} (hn : n ≠ 0) :
    counit (R := k) (gradeProj 𝒜 n a) = 0 := by
  rw [h𝒜.counit_gradeProj]; simp [hn]

/-- The augmentation ideal is homogeneous. -/
theorem gradeProj_mem_ker_counit (n : ι) {a : A} (ha : counit (R := k) a = 0) :
    counit (R := k) (gradeProj 𝒜 n a) = 0 := by
  rw [h𝒜.counit_gradeProj]; simp [ha]

/-- Every homogeneous component of a primitive element is primitive. -/
theorem isPrimitiveElem_gradeProj {f : A} (hf : Bialgebra.IsPrimitiveElem k f) (n : ι) :
    Bialgebra.IsPrimitiveElem k (gradeProj 𝒜 n f) where
  counit_eq_zero := h𝒜.gradeProj_mem_ker_counit n hf.counit_eq_zero
  comul_eq_tmul_add_tmul := by
    rw [h𝒜.comul_gradeProj, hf.comul_eq_tmul_add_tmul, map_add,
      tensorProj_tmul_of_mem_left 𝒜 𝒜 n (one_mem_zero 𝒜),
      tensorProj_tmul_of_mem_right 𝒜 𝒜 n _ (one_mem_zero 𝒜), sub_zero]

end IsGradedBialgebra

end Bialgebra

end Langlands.Algebra.GradedHopf
