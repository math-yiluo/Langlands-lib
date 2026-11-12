import Langlands.GroupScheme.Quaternionic.FormLemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Central weights of matrix isometries and totally isotropic subspaces -/

noncomputable section

universe u v w z

open Matrix

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n : Type w} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem sesqForm_eq_dotProduct (H : Matrix n n D) (x y : n → D) :
    σ.sesqForm H x y = x ⬝ᵥ (H *ᵥ (σ ∘ y)) := by
  simp [sesqForm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem map_vecMul (A : Matrix n n D) (y : n → D) :
    σ ∘ (y ᵥ* A) = σ.matrix n A *ᵥ (σ ∘ y) := by
  ext i
  simp [vecMul, mulVec, dotProduct, σ.map_sum, σ.map_mul, matrix_apply]

/-- Change of Gram matrix under the row-vector action. -/
theorem sesqForm_vecMul (H A : Matrix n n D) (x y : n → D) :
    σ.sesqForm H (x ᵥ* A) (y ᵥ* A) =
      σ.sesqForm (A * H * σ.matrix n A) x y := by
  simp only [σ.sesqForm_eq_dotProduct, σ.map_vecMul, mulVec_mulVec,
    dotProduct_mulVec, vecMul_vecMul, Matrix.mul_assoc]

theorem sesqForm_vecMul_of_isometry {H A : Matrix n n D}
    (hA : A * H * σ.matrix n A = H) (x y : n → D) :
    σ.sesqForm H (x ᵥ* A) (y ᵥ* A) = σ.sesqForm H x y := by
  rw [σ.sesqForm_vecMul, hA]

omit [DecidableEq n] in
theorem sesqForm_smul_left_scalar (H : Matrix n n D) (a : K) (x y : n → D) :
    σ.sesqForm H (a • x) y = a • σ.sesqForm H x y := by
  simp [sesqForm, Finset.smul_sum]

omit [DecidableEq n] in
theorem sesqForm_smul_right_scalar (H : Matrix n n D) (a : K) (x y : n → D) :
    σ.sesqForm H x (a • y) = a • σ.sesqForm H x y := by
  simp [sesqForm, Finset.smul_sum]

/-- Isometry eigenvectors with central eigenvalues pair trivially unless the
eigenvalues are reciprocal. -/
theorem sesqForm_eq_zero_of_eigenvectors {H A : Matrix n n D}
    (hA : A * H * σ.matrix n A = H) {a b : K} {x y : n → D}
    (hx : x ᵥ* A = a • x) (hy : y ᵥ* A = b • y) (hab : a * b ≠ 1) :
    σ.sesqForm H x y = 0 := by
  have h := σ.sesqForm_vecMul_of_isometry hA x y
  rw [hx, hy, σ.sesqForm_smul_left_scalar, σ.sesqForm_smul_right_scalar,
    smul_smul] at h
  have hz : (a * b - 1) • σ.sesqForm H x y = 0 := by
    rw [sub_smul, one_smul, h, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hab)

variable {I : Type z}

/-- The common eigenspace for a family of matrices and central scalar weights,
as a left vector space over the division algebra. -/
def commonWeightSpace (A : I → Matrix n n D) (χ : I → K) :
    Submodule D (n → D) where
  carrier := {x | ∀ t, x ᵥ* A t = χ t • x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy t
    simp only [add_vecMul, hx t, hy t, smul_add]
  smul_mem' := by
    intro a x hx t
    rw [smul_vecMul, hx t, smul_comm]

omit [DecidableEq n] in
@[simp] theorem mem_commonWeightSpace (A : I → Matrix n n D) (χ : I → K)
    (x : n → D) :
    x ∈ commonWeightSpace A χ ↔ ∀ t, x ᵥ* A t = χ t • x := Iff.rfl

/-- A single family member with nonreciprocal weights forces orthogonality of
the two entire division-algebra weight spaces. -/
theorem sesqForm_commonWeightSpace_eq_zero {H : Matrix n n D}
    {A : I → Matrix n n D} (hA : ∀ t, A t * H * σ.matrix n (A t) = H)
    {χ ψ : I → K} (hχψ : ∃ t, χ t * ψ t ≠ 1)
    {x y : n → D} (hx : x ∈ commonWeightSpace A χ)
    (hy : y ∈ commonWeightSpace A ψ) :
    σ.sesqForm H x y = 0 := by
  obtain ⟨t, ht⟩ := hχψ
  exact σ.sesqForm_eq_zero_of_eigenvectors (hA t) (hx t) (hy t) ht

theorem isTotallyIsotropic_commonWeightSpace {H : Matrix n n D}
    {A : I → Matrix n n D} (hA : ∀ t, A t * H * σ.matrix n (A t) = H)
    {χ : I → K} (hχ : ∃ t, χ t * χ t ≠ 1) :
    σ.IsTotallyIsotropic H (commonWeightSpace A χ) :=
  fun _ hx _ hy => σ.sesqForm_commonWeightSpace_eq_zero hA hχ hx hy

/-- The sum of two individually isotropic, mutually orthogonal weight spaces is
totally isotropic. The three separating family members may differ. -/
theorem isTotallyIsotropic_sup_commonWeightSpace {H : Matrix n n D}
    {A : I → Matrix n n D} (hA : ∀ t, A t * H * σ.matrix n (A t) = H)
    {χ ψ : I → K} (hχ : ∃ t, χ t * χ t ≠ 1)
    (hψ : ∃ t, ψ t * ψ t ≠ 1) (hχψ : ∃ t, χ t * ψ t ≠ 1) :
    σ.IsTotallyIsotropic H (commonWeightSpace A χ ⊔ commonWeightSpace A ψ) := by
  intro x hx y hy
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
  rw [σ.sesqForm_add_left, σ.sesqForm_add_right, σ.sesqForm_add_right]
  have hψχ : ∃ t, ψ t * χ t ≠ 1 := by
    simpa only [mul_comm] using hχψ
  rw [σ.sesqForm_commonWeightSpace_eq_zero hA hχ hx₁ hy₁,
    σ.sesqForm_commonWeightSpace_eq_zero hA hχψ hx₁ hy₂,
    σ.sesqForm_commonWeightSpace_eq_zero hA hψχ hx₂ hy₁,
    σ.sesqForm_commonWeightSpace_eq_zero hA hψ hx₂ hy₂]
  simp

omit [DecidableEq n] in
/-- Distinct central weight functions have disjoint common eigenspaces. -/
theorem disjoint_commonWeightSpace {A : I → Matrix n n D} {χ ψ : I → K}
    (hχψ : χ ≠ ψ) :
    Disjoint (commonWeightSpace A χ) (commonWeightSpace A ψ) := by
  rw [Submodule.disjoint_def]
  intro x hx hy
  by_contra hzero
  apply hχψ
  funext t
  apply smul_left_injective K hzero
  exact (hx t).symm.trans (hy t)

/-- Two nonzero, distinct weight spaces with nonreciprocal weights force Witt
index at least two. -/
theorem two_le_wittIndex_of_commonWeightSpaces {H : Matrix n n D}
    {A : I → Matrix n n D} (hA : ∀ t, A t * H * σ.matrix n (A t) = H)
    {χ ψ : I → K} (hχ : ∃ t, χ t * χ t ≠ 1)
    (hψ : ∃ t, ψ t * ψ t ≠ 1) (hχψ : ∃ t, χ t * ψ t ≠ 1)
    (hne : χ ≠ ψ) (hWχ : commonWeightSpace A χ ≠ ⊥)
    (hWψ : commonWeightSpace A ψ ≠ ⊥) :
    2 ≤ σ.wittIndex H := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (commonWeightSpace A χ) (commonWeightSpace A ψ)
  rw [(disjoint_commonWeightSpace hne).eq_bot, finrank_bot, add_zero] at hdim
  have hχpos : 0 < Module.finrank D (commonWeightSpace A χ) :=
    Nat.pos_of_ne_zero (fun hz => hWχ (Submodule.finrank_eq_zero.mp hz))
  have hψpos : 0 < Module.finrank D (commonWeightSpace A ψ) :=
    Nat.pos_of_ne_zero (fun hz => hWψ (Submodule.finrank_eq_zero.mp hz))
  have hle := σ.finrank_le_wittIndex
    (σ.isTotallyIsotropic_sup_commonWeightSpace hA hχ hψ hχψ)
  omega

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
