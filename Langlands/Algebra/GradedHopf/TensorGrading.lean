import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-! # Degree projections on tensor products of graded modules -/

noncomputable section

open TensorProduct DirectSum

namespace Langlands.Algebra.GradedHopf

variable {ι k M N M' N' : Type*} [DecidableEq ι] [CommRing k]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]
  [AddCommGroup M'] [Module k M'] [AddCommGroup N'] [Module k N']

section GradeProj

variable (ℳ : ι → Submodule k M) [Decomposition ℳ]

/-- The linear projection of a decomposed module onto its summand of degree `i`. -/
def gradeProj (i : ι) : M →ₗ[k] M :=
  (ℳ i).subtype ∘ₗ DirectSum.component k ι (fun i => ℳ i) i ∘ₗ
    (decomposeLinearEquiv ℳ).toLinearMap

theorem gradeProj_apply (i : ι) (m : M) : gradeProj ℳ i m = (decompose ℳ m i : M) := rfl

theorem gradeProj_mem (i : ι) (m : M) : gradeProj ℳ i m ∈ ℳ i := (decompose ℳ m i).2

theorem gradeProj_of_mem {i j : ι} {m : M} (hm : m ∈ ℳ j) :
    gradeProj ℳ i m = if j = i then m else 0 := by
  rw [gradeProj_apply]
  split_ifs with h
  · subst h
    exact decompose_of_mem_same ℳ hm
  · exact decompose_of_mem_ne ℳ hm h

theorem gradeProj_of_mem_self {i : ι} {m : M} (hm : m ∈ ℳ i) : gradeProj ℳ i m = m := by
  simp [gradeProj_of_mem ℳ hm]

theorem gradeProj_of_mem_ne {i j : ι} {m : M} (hm : m ∈ ℳ j) (h : j ≠ i) :
    gradeProj ℳ i m = 0 := by
  simp [gradeProj_of_mem ℳ hm, h]

theorem mem_iff_gradeProj {i : ι} {m : M} : m ∈ ℳ i ↔ gradeProj ℳ i m = m :=
  ⟨gradeProj_of_mem_self ℳ, fun h => h ▸ gradeProj_mem ℳ i m⟩

/-- Every element is the finite sum of its homogeneous components. -/
theorem sum_gradeProj [∀ (i) (x : ℳ i), Decidable (x ≠ 0)] (m : M) :
    ∑ i ∈ (decompose ℳ m).support, gradeProj ℳ i m = m :=
  sum_support_decompose ℳ m

/-- Two elements agree once all their homogeneous components agree. -/
theorem ext_gradeProj {m m' : M} (h : ∀ i, gradeProj ℳ i m = gradeProj ℳ i m') : m = m' := by
  apply (decompose ℳ).injective
  ext i
  exact h i

variable {ℳ} {ℳ' : ι → Submodule k M'} [Decomposition ℳ']

/-- A linear map is graded if it maps each summand into the summand of the same degree. -/
def IsGradedMap (f : M →ₗ[k] M') : Prop := ∀ i, ∀ m ∈ ℳ i, f m ∈ ℳ' i

theorem IsGradedMap.comp_gradeProj {f : M →ₗ[k] M'} (hf : IsGradedMap (ℳ := ℳ) (ℳ' := ℳ') f)
    (i : ι) : f ∘ₗ gradeProj ℳ i = gradeProj ℳ' i ∘ₗ f := by
  refine decompose_lhom_ext ℳ fun j => LinearMap.ext fun m => ?_
  simp only [LinearMap.comp_apply, Submodule.coe_subtype]
  rw [gradeProj_of_mem ℳ m.2, gradeProj_of_mem ℳ' (hf j m m.2)]
  split_ifs <;> simp

theorem IsGradedMap.gradeProj_apply {f : M →ₗ[k] M'} (hf : IsGradedMap (ℳ := ℳ) (ℳ' := ℳ') f)
    (i : ι) (m : M) : f (gradeProj ℳ i m) = gradeProj ℳ' i (f m) :=
  LinearMap.congr_fun (hf.comp_gradeProj i) m

end GradeProj

section TensorProj

variable [AddCommGroup ι] (ℳ : ι → Submodule k M) (𝒩 : ι → Submodule k N)

/-- The submodule of `M ⊗ N` spanned by pure tensors of homogeneous elements of total
degree `n`. -/
def tensorGrade (n : ι) : Submodule k (M ⊗[k] N) :=
  Submodule.span k {x | ∃ i j a b, a ∈ ℳ i ∧ b ∈ 𝒩 j ∧ i + j = n ∧ a ⊗ₜ[k] b = x}

omit [DecidableEq ι] in
theorem tmul_mem_tensorGrade {i j : ι} {a : M} {b : N} (ha : a ∈ ℳ i) (hb : b ∈ 𝒩 j) :
    a ⊗ₜ[k] b ∈ tensorGrade ℳ 𝒩 (i + j) :=
  Submodule.subset_span ⟨i, j, a, b, ha, hb, rfl, rfl⟩

variable [Decomposition ℳ] [Decomposition 𝒩]

/-- The projection of `M ⊗ N` onto the part of total degree `n`. -/
def tensorProj (n : ι) : M ⊗[k] N →ₗ[k] M ⊗[k] N :=
  DirectSum.toModule k (ι × ι) (M ⊗[k] N)
      (fun p => if p.1 + p.2 = n then TensorProduct.map (ℳ p.1).subtype (𝒩 p.2).subtype
        else 0) ∘ₗ
    (TensorProduct.directSum k k (fun i => ℳ i) (fun j => 𝒩 j)).toLinearMap ∘ₗ
    TensorProduct.map (decomposeLinearEquiv ℳ).toLinearMap (decomposeLinearEquiv 𝒩).toLinearMap

theorem tensorProj_tmul_of_mem (n : ι) {i j : ι} {a : M} {b : N} (ha : a ∈ ℳ i)
    (hb : b ∈ 𝒩 j) :
    tensorProj ℳ 𝒩 n (a ⊗ₜ[k] b) = if i + j = n then a ⊗ₜ[k] b else 0 := by
  have h1 : decomposeLinearEquiv ℳ a = lof k ι (fun i => ℳ i) i ⟨a, ha⟩ :=
    decomposeLinearEquiv_apply_coe ℳ i ⟨a, ha⟩
  have h2 : decomposeLinearEquiv 𝒩 b = lof k ι (fun i => 𝒩 i) j ⟨b, hb⟩ :=
    decomposeLinearEquiv_apply_coe 𝒩 j ⟨b, hb⟩
  simp only [tensorProj, LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
    h1, h2, directSum_lof_tmul_lof, toModule_lof]
  split_ifs <;> simp

theorem tensorProj_of_mem_tensorGrade {n m : ι} {x : M ⊗[k] N} (hx : x ∈ tensorGrade ℳ 𝒩 m) :
    tensorProj ℳ 𝒩 n x = if m = n then x else 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, j, a, b, ha, hb, rfl, rfl⟩ := hx
    exact tensorProj_tmul_of_mem ℳ 𝒩 n ha hb
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, hx, hy]
    split_ifs <;> simp
  | smul c x _ hx =>
    rw [map_smul, hx]
    split_ifs <;> simp

theorem tensorProj_of_mem_tensorGrade_self {n : ι} {x : M ⊗[k] N}
    (hx : x ∈ tensorGrade ℳ 𝒩 n) : tensorProj ℳ 𝒩 n x = x := by
  simp [tensorProj_of_mem_tensorGrade ℳ 𝒩 hx]

theorem tensorProj_of_mem_tensorGrade_ne {n m : ι} {x : M ⊗[k] N}
    (hx : x ∈ tensorGrade ℳ 𝒩 m) (h : m ≠ n) : tensorProj ℳ 𝒩 n x = 0 := by
  simp [tensorProj_of_mem_tensorGrade ℳ 𝒩 hx, h]

omit [AddCommGroup ι] in
/-- Induction on `M ⊗ N` through pure tensors of homogeneous elements. -/
theorem tensorProduct_induction {motive : M ⊗[k] N → Prop} (zero : motive 0)
    (hom : ∀ {i j : ι} {a : M} {b : N}, a ∈ ℳ i → b ∈ 𝒩 j → motive (a ⊗ₜ[k] b))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : ∀ x, motive x := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact zero
  | tmul a b =>
    induction a using Decomposition.inductionOn ℳ with
    | zero => simpa using zero
    | homogeneous a =>
      induction b using Decomposition.inductionOn 𝒩 with
      | zero => simpa using zero
      | homogeneous b => exact hom a.2 b.2
      | add b b' hb hb' => rw [tmul_add]; exact add _ _ hb hb'
    | add a a' ha ha' => rw [add_tmul]; exact add _ _ ha ha'
  | add x y hx hy => exact add _ _ hx hy

theorem tensorProj_mem_tensorGrade (n : ι) (x : M ⊗[k] N) :
    tensorProj ℳ 𝒩 n x ∈ tensorGrade ℳ 𝒩 n := by
  induction x using tensorProduct_induction ℳ 𝒩 with
  | zero => simp
  | hom ha hb =>
    rw [tensorProj_tmul_of_mem ℳ 𝒩 n ha hb]
    split_ifs with h
    · exact h ▸ tmul_mem_tensorGrade ℳ 𝒩 ha hb
    · exact zero_mem _
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem mem_tensorGrade_iff {n : ι} {x : M ⊗[k] N} :
    x ∈ tensorGrade ℳ 𝒩 n ↔ tensorProj ℳ 𝒩 n x = x :=
  ⟨tensorProj_of_mem_tensorGrade_self ℳ 𝒩, fun h => h ▸ tensorProj_mem_tensorGrade ℳ 𝒩 n x⟩

theorem tensorProj_tmul_of_mem_right (n : ι) {j : ι} (a : M) {b : N} (hb : b ∈ 𝒩 j) :
    tensorProj ℳ 𝒩 n (a ⊗ₜ[k] b) = gradeProj ℳ (n - j) a ⊗ₜ[k] b := by
  induction a using Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous i' a =>
    rw [tensorProj_tmul_of_mem ℳ 𝒩 n a.2 hb, gradeProj_of_mem ℳ a.2]
    by_cases h : i' + j = n
    · rw [if_pos h, if_pos (eq_sub_of_add_eq h)]
    · rw [if_neg h, if_neg (fun h' => h (eq_sub_iff_add_eq.mp h')), zero_tmul]
  | add a a' ha ha' => rw [add_tmul, map_add, ha, ha', map_add, add_tmul]

theorem tensorProj_tmul_of_mem_left (n : ι) {i : ι} {a : M} (ha : a ∈ ℳ i) (b : N) :
    tensorProj ℳ 𝒩 n (a ⊗ₜ[k] b) = a ⊗ₜ[k] gradeProj 𝒩 (n - i) b := by
  induction b using Decomposition.inductionOn 𝒩 with
  | zero => simp
  | @homogeneous j' b =>
    rw [tensorProj_tmul_of_mem ℳ 𝒩 n ha b.2, gradeProj_of_mem 𝒩 b.2]
    by_cases h : i + j' = n
    · rw [if_pos h, if_pos (eq_sub_of_add_eq' h)]
    · rw [if_neg h, if_neg (fun h' => h (by rw [h']; abel)), tmul_zero]
  | add b b' hb hb' => rw [tmul_add, map_add, hb, hb', map_add, tmul_add]

variable {ℳ 𝒩} {ℳ' : ι → Submodule k M'} {𝒩' : ι → Submodule k N'}

omit [DecidableEq ι] [Decomposition ℳ] [Decomposition 𝒩] in
theorem IsGradedMap.map_tensorGrade
    {f : M →ₗ[k] M'} {g : N →ₗ[k] N'}
    (hf : IsGradedMap (ℳ := ℳ) (ℳ' := ℳ') f) (hg : IsGradedMap (ℳ := 𝒩) (ℳ' := 𝒩') g)
    {n : ι} {x : M ⊗[k] N} (hx : x ∈ tensorGrade ℳ 𝒩 n) :
    TensorProduct.map f g x ∈ tensorGrade ℳ' 𝒩' n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, j, a, b, ha, hb, rfl, rfl⟩ := hx
    rw [TensorProduct.map_tmul]
    exact tmul_mem_tensorGrade ℳ' 𝒩' (hf i a ha) (hg j b hb)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem IsGradedMap.map_comp_tensorProj [Decomposition ℳ'] [Decomposition 𝒩']
    {f : M →ₗ[k] M'} {g : N →ₗ[k] N'}
    (hf : IsGradedMap (ℳ := ℳ) (ℳ' := ℳ') f) (hg : IsGradedMap (ℳ := 𝒩) (ℳ' := 𝒩') g)
    (n : ι) :
    TensorProduct.map f g ∘ₗ tensorProj ℳ 𝒩 n = tensorProj ℳ' 𝒩' n ∘ₗ TensorProduct.map f g := by
  refine TensorProduct.ext' fun a b => ?_
  induction a using Decomposition.inductionOn ℳ with
  | zero => simp
  | homogeneous a =>
    induction b using Decomposition.inductionOn 𝒩 with
    | zero => simp
    | homogeneous b =>
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul]
      rw [tensorProj_tmul_of_mem ℳ 𝒩 n a.2 b.2,
        tensorProj_tmul_of_mem ℳ' 𝒩' n (hf _ a a.2) (hg _ b b.2)]
      split_ifs <;> simp
    | add b b' hb hb' => simp only [tmul_add, map_add] at hb hb' ⊢; rw [hb, hb']
  | add a a' ha ha' => simp only [add_tmul, map_add] at ha ha' ⊢; rw [ha, ha']

end TensorProj

end Langlands.Algebra.GradedHopf
