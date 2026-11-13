import Langlands.GroupScheme.Examples.HermitianMatrixBasic
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! # Reindexing actual Hermitian matrix point groups -/

namespace Langlands.GroupScheme.HermitianMatrix

open SU3Root

universe u v w x y

variable {A : Type u} {B : Type v} {ι : Type w} {κ : Type x} {μ : Type y}
  [CommRing A] [CommRing B]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ]
  {c : RingInvolution A} {d : RingInvolution B}

/-- Relabel the rows and columns of an actual invertible matrix. -/
def reindexGL (r : ι ≃ κ) :
    Matrix.GeneralLinearGroup ι A ≃* Matrix.GeneralLinearGroup κ A :=
  Units.mapEquiv (Matrix.reindexRingEquiv A r).toMulEquiv

@[simp] theorem reindexGL_val (r : ι ≃ κ) (g : Matrix.GeneralLinearGroup ι A) :
    (reindexGL r g : Matrix κ κ A) = Matrix.reindex r r (g : Matrix ι ι A) := rfl

@[simp] theorem reindexGL_symm (r : ι ≃ κ) :
    (reindexGL (A := A) r).symm = reindexGL r.symm := rfl

@[simp] theorem reindexGL_refl (g : Matrix.GeneralLinearGroup ι A) :
    reindexGL (Equiv.refl ι) g = g := by
  apply Units.ext
  rfl

theorem reindexGL_trans (r : ι ≃ κ) (s : κ ≃ μ)
    (g : Matrix.GeneralLinearGroup ι A) :
    reindexGL s (reindexGL r g) = reindexGL (r.trans s) g := by
  apply Units.ext
  rfl

/-- Relabeling both axes leaves the determinant unchanged, including its unit value. -/
@[simp] theorem reindexGL_det (r : ι ≃ κ) (g : Matrix.GeneralLinearGroup ι A) :
    Matrix.GeneralLinearGroup.det (reindexGL r g) = Matrix.GeneralLinearGroup.det g := by
  apply Units.ext
  exact Matrix.det_reindex_self r (g : Matrix ι ι A)

/-- Relabeling commutes with every entrywise coefficient change. -/
theorem reindexGL_map (r : ι ≃ κ) (f : A →+* B)
    (g : Matrix.GeneralLinearGroup ι A) :
    reindexGL r (Matrix.GeneralLinearGroup.map f g) =
      Matrix.GeneralLinearGroup.map f (reindexGL r g) := by
  apply Units.ext
  rfl

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
@[simp] theorem adjoint_reindex (r : ι ≃ κ) (M : Matrix ι ι A) :
    adjoint c (Matrix.reindex r r M) = Matrix.reindex r r (adjoint c M) := rfl

namespace Form

/-- A relabeling of a nonsingular Hermitian form retains the reindexed Gram matrix. -/
def reindex (H : Form c ι) (r : ι ≃ κ) : Form c κ where
  gram := reindexGL r H.gram
  hermitian := by
    change adjoint c (Matrix.reindex r r (H.gram : Matrix ι ι A)) =
      Matrix.reindex r r (H.gram : Matrix ι ι A)
    rw [adjoint_reindex, H.hermitian]

@[simp] theorem reindex_gram (H : Form c ι) (r : ι ≃ κ) :
    (H.reindex r).gram = reindexGL r H.gram := rfl

@[simp] theorem reindex_refl (H : Form c ι) : H.reindex (Equiv.refl ι) = H := by
  apply Form.ext
  exact reindexGL_refl H.gram

theorem reindex_trans (H : Form c ι) (r : ι ≃ κ) (s : κ ≃ μ) :
    (H.reindex r).reindex s = H.reindex (r.trans s) := by
  apply Form.ext
  exact reindexGL_trans r s H.gram

@[simp] theorem reindex_symm (H : Form c ι) (r : ι ≃ κ) :
    (H.reindex r).reindex r.symm = H := by
  apply Form.ext
  exact (reindexGL r).symm_apply_apply H.gram

/-- Scalar extension and relabeling give the same actual Gram form. -/
theorem reindex_map (H : Form c ι) (r : ι ≃ κ) (f : A →+* B)
    (hf : ∀ a, f (c.bar a) = d.bar (f a)) :
    (H.reindex r).map f hf = (H.map f hf).reindex r := by
  apply Form.ext
  exact (reindexGL_map r f H.gram).symm

end Form

/-- The full Gram-preservation equation is invariant under relabeling. -/
theorem preserves_reindex_iff (H : Form c ι) (r : ι ≃ κ) (M : Matrix ι ι A) :
    Preserves (H.reindex r) (Matrix.reindex r r M) ↔ Preserves H M := by
  unfold Preserves
  rw [adjoint_reindex]
  change (Matrix.reindexRingEquiv A r) (adjoint c M) *
      (Matrix.reindexRingEquiv A r) (H.gram : Matrix ι ι A) *
      (Matrix.reindexRingEquiv A r) M =
        (Matrix.reindexRingEquiv A r) (H.gram : Matrix ι ι A) ↔ _
  rw [← map_mul, ← map_mul]
  exact (Matrix.reindexRingEquiv A r).injective.eq_iff

/-- The two defining subgroup equations survive reindexing in both directions. -/
@[simp] theorem mem_specialUnitarySubgroup_reindex_iff (H : Form c ι) (r : ι ≃ κ)
    (g : Matrix.GeneralLinearGroup ι A) :
    reindexGL r g ∈ specialUnitarySubgroup (H.reindex r) ↔
      g ∈ specialUnitarySubgroup H := by
  change Preserves (H.reindex r) (Matrix.reindex r r (g : Matrix ι ι A)) ∧
      Matrix.GeneralLinearGroup.det (reindexGL r g) = 1 ↔ _
  rw [preserves_reindex_iff, reindexGL_det]
  rfl

/-- Relabeling gives an equivalence of the actual determinant-one isometry groups. -/
def specialUnitaryReindexEquiv (H : Form c ι) (r : ι ≃ κ) :
    specialUnitarySubgroup H ≃* specialUnitarySubgroup (H.reindex r) where
  toFun g := ⟨reindexGL r g.1,
    (mem_specialUnitarySubgroup_reindex_iff H r g.1).mpr g.2⟩
  invFun g := ⟨(reindexGL r).symm g.1,
    (mem_specialUnitarySubgroup_reindex_iff H r ((reindexGL r).symm g.1)).mp
      (by simpa only [MulEquiv.apply_symm_apply] using g.2)⟩
  left_inv g := Subtype.ext ((reindexGL r).symm_apply_apply g.1)
  right_inv g := Subtype.ext ((reindexGL r).apply_symm_apply g.1)
  map_mul' g h := Subtype.ext ((reindexGL r).map_mul g.1 h.1)

@[simp] theorem specialUnitaryReindexEquiv_val (H : Form c ι) (r : ι ≃ κ)
    (g : specialUnitarySubgroup H) :
    (specialUnitaryReindexEquiv H r g).1 = reindexGL r g.1 := rfl

@[simp] theorem specialUnitaryReindexEquiv_matrix (H : Form c ι) (r : ι ≃ κ)
    (g : specialUnitarySubgroup H) :
    ((specialUnitaryReindexEquiv H r g).1 : Matrix κ κ A) =
      Matrix.reindex r r (g.1 : Matrix ι ι A) := rfl

@[simp] theorem specialUnitaryReindexEquiv_symm_matrix (H : Form c ι) (r : ι ≃ κ)
    (g : specialUnitarySubgroup (H.reindex r)) :
    (((specialUnitaryReindexEquiv H r).symm g).1 : Matrix ι ι A) =
      Matrix.reindex r.symm r.symm (g.1 : Matrix κ κ A) := rfl

/-- The compatibility of Gram matrices for a coefficient map reindexes entrywise. -/
theorem reindex_gram_map {H : Form c ι} {J : Form d ι}
    (r : ι ≃ κ) (f : A →+* B)
    (hJ : (H.gram : Matrix ι ι A).map f = J.gram) :
    ((H.reindex r).gram : Matrix κ κ A).map f = (J.reindex r).gram :=
  congrArg (Matrix.reindex r r) hJ

/-- Reindexing actual determinant-one isometries commutes with coefficient maps. -/
theorem specialUnitaryReindexEquiv_map {H : Form c ι} {J : Form d ι}
    (r : ι ≃ κ) (f : A →+* B)
    (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hJ : (H.gram : Matrix ι ι A).map f = J.gram) (g : specialUnitarySubgroup H) :
    coefficientMap f hf (reindex_gram_map r f hJ) (specialUnitaryReindexEquiv H r g) =
      specialUnitaryReindexEquiv J r (coefficientMap f hf hJ g) := by
  apply Subtype.ext
  exact (reindexGL_map r f g.1).symm

end Langlands.GroupScheme.HermitianMatrix
