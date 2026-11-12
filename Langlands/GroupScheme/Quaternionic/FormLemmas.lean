import Langlands.GroupScheme.Quaternionic.Forms
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-! # Elementary tools for quaternionic forms and their Witt indices -/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n : Type w} [Fintype n] [DecidableEq n]

@[simp] theorem sesqForm_zero_left (H : Matrix n n D) (y : n → D) :
    σ.sesqForm H 0 y = 0 := by
  simp [sesqForm]

@[simp] theorem sesqForm_zero_right (H : Matrix n n D) (x : n → D) :
    σ.sesqForm H x 0 = 0 := by
  simp [sesqForm]

theorem sesqForm_add_left (H : Matrix n n D) (x x' y : n → D) :
    σ.sesqForm H (x + x') y = σ.sesqForm H x y + σ.sesqForm H x' y := by
  simp [sesqForm, add_mul, Finset.sum_add_distrib]

theorem sesqForm_add_right (H : Matrix n n D) (x y y' : n → D) :
    σ.sesqForm H x (y + y') = σ.sesqForm H x y + σ.sesqForm H x y' := by
  simp [sesqForm, mul_add, Finset.sum_add_distrib]

theorem sesqForm_smul_left (H : Matrix n n D) (a : D) (x y : n → D) :
    σ.sesqForm H (a • x) y = a * σ.sesqForm H x y := by
  simp [sesqForm, mul_assoc, Finset.mul_sum]

theorem sesqForm_smul_right (H : Matrix n n D) (a : D) (x y : n → D) :
    σ.sesqForm H x (a • y) = σ.sesqForm H x y * σ a := by
  simp [sesqForm, mul_assoc, Finset.sum_mul]

theorem map_sesqForm (H : Matrix n n D) (x y : n → D) :
    σ (σ.sesqForm H x y) = σ.sesqForm (σ.matrix n H) y x := by
  simp only [sesqForm, map_sum, map_mul, apply_apply, matrix_apply, mul_assoc]
  exact Finset.sum_comm

theorem sesqForm_neg_matrix (H : Matrix n n D) (x y : n → D) :
    σ.sesqForm (-H) x y = -σ.sesqForm H x y := by
  simp [sesqForm]

theorem IsAntihermitian.sesqForm_swap {H : Matrix n n D}
    (hH : σ.IsAntihermitian H) (x y : n → D) :
    σ.sesqForm H y x = -σ (σ.sesqForm H x y) := by
  rw [σ.map_sesqForm, hH.1, σ.sesqForm_neg_matrix, neg_neg]

@[simp] theorem isTotallyIsotropic_bot (H : Matrix n n D) :
    σ.IsTotallyIsotropic H ⊥ := by
  intro x hx y hy
  simp only [Submodule.mem_bot] at hx hy
  simp [hx]

theorem IsTotallyIsotropic.mono {H : Matrix n n D}
    {W W' : Submodule D (n → D)} (hW : σ.IsTotallyIsotropic H W) (h : W' ≤ W) :
    σ.IsTotallyIsotropic H W' :=
  fun x hx y hy => hW x (h hx) y (h hy)

theorem isTotallyIsotropic_span_singleton_iff (H : Matrix n n D) (x : n → D) :
    σ.IsTotallyIsotropic H (D ∙ x) ↔ σ.sesqForm H x x = 0 := by
  constructor
  · intro h
    exact h x (Submodule.mem_span_singleton_self x)
      x (Submodule.mem_span_singleton_self x)
  · intro h y hy z hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hz
    simp [σ.sesqForm_smul_left, σ.sesqForm_smul_right, h]

private theorem isotropic_dimensions_nonempty (H : Matrix n n D) :
    {r | ∃ W : Submodule D (n → D),
      σ.IsTotallyIsotropic H W ∧ Module.finrank D W = r}.Nonempty := by
  exact ⟨0, ⊥, σ.isTotallyIsotropic_bot H, by simp⟩

private theorem isotropic_dimensions_bddAbove (H : Matrix n n D) :
    BddAbove {r | ∃ W : Submodule D (n → D),
      σ.IsTotallyIsotropic H W ∧ Module.finrank D W = r} := by
  refine ⟨Fintype.card n, ?_⟩
  rintro r ⟨W, _, rfl⟩
  simpa using Submodule.finrank_le W

theorem finrank_le_wittIndex {H : Matrix n n D} {W : Submodule D (n → D)}
    (hW : σ.IsTotallyIsotropic H W) : Module.finrank D W ≤ σ.wittIndex H :=
  le_csSup (σ.isotropic_dimensions_bddAbove H) ⟨W, hW, rfl⟩

theorem wittIndex_le_card (H : Matrix n n D) : σ.wittIndex H ≤ Fintype.card n := by
  apply csSup_le (σ.isotropic_dimensions_nonempty H)
  rintro r ⟨W, _, rfl⟩
  simpa using Submodule.finrank_le W

theorem exists_isTotallyIsotropic_finrank_eq_wittIndex (H : Matrix n n D) :
    ∃ W : Submodule D (n → D),
      σ.IsTotallyIsotropic H W ∧ Module.finrank D W = σ.wittIndex H := by
  exact (σ.isotropic_dimensions_nonempty H).csSup_mem
    ((Set.finite_Iic (Fintype.card n)).subset (by
      rintro r ⟨W, _, rfl⟩
      simpa using Submodule.finrank_le W))

/-- A chosen totally isotropic subspace whose dimension is the Witt index. -/
def wittSubspace (H : Matrix n n D) : Submodule D (n → D) :=
  (σ.exists_isTotallyIsotropic_finrank_eq_wittIndex H).choose

theorem isTotallyIsotropic_wittSubspace (H : Matrix n n D) :
    σ.IsTotallyIsotropic H (σ.wittSubspace H) :=
  (σ.exists_isTotallyIsotropic_finrank_eq_wittIndex H).choose_spec.1

@[simp] theorem finrank_wittSubspace (H : Matrix n n D) :
    Module.finrank D (σ.wittSubspace H) = σ.wittIndex H :=
  (σ.exists_isTotallyIsotropic_finrank_eq_wittIndex H).choose_spec.2

theorem wittIndex_le_iff (H : Matrix n n D) (r : ℕ) :
    σ.wittIndex H ≤ r ↔ ∀ W : Submodule D (n → D),
      σ.IsTotallyIsotropic H W → Module.finrank D W ≤ r := by
  constructor
  · intro h W hW
    exact (σ.finrank_le_wittIndex hW).trans h
  · intro h
    obtain ⟨W, hW, hdim⟩ := σ.exists_isTotallyIsotropic_finrank_eq_wittIndex H
    simpa [hdim] using h W hW

theorem wittIndex_pos_iff (H : Matrix n n D) :
    0 < σ.wittIndex H ↔ ∃ x : n → D, x ≠ 0 ∧ σ.sesqForm H x x = 0 := by
  constructor
  · intro h
    obtain ⟨W, hW, hdim⟩ := σ.exists_isTotallyIsotropic_finrank_eq_wittIndex H
    have : Nontrivial W := (Module.finrank_pos_iff.mp (hdim.symm ▸ h))
    obtain ⟨x, hx⟩ := exists_ne (0 : W)
    exact ⟨x, fun h => hx (Subtype.ext h), hW x x.property x x.property⟩
  · rintro ⟨x, hx, hxx⟩
    have h := σ.finrank_le_wittIndex
      ((σ.isTotallyIsotropic_span_singleton_iff H x).mpr hxx)
    rw [finrank_span_singleton hx] at h
    exact h

theorem wittIndex_eq_one_iff (H : Matrix n n D) :
    σ.wittIndex H = 1 ↔
      (∃ x : n → D, x ≠ 0 ∧ σ.sesqForm H x x = 0) ∧
        ∀ W : Submodule D (n → D), σ.IsTotallyIsotropic H W →
          Module.finrank D W ≤ 1 := by
  rw [← σ.wittIndex_pos_iff, ← σ.wittIndex_le_iff]
  omega

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
