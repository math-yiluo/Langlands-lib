import Langlands.GroupScheme.Examples.SU3RootParameters
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Nonsingular Hermitian Gram matrices and their actual isometry groups -/

namespace Langlands.GroupScheme.HermitianMatrix

open SU3Root

universe u v w z

variable {A : Type u} {B : Type w} {C : Type z} {ι : Type v}
  [CommRing A] [CommRing B] [CommRing C] [Fintype ι] [DecidableEq ι]
  {c : RingInvolution A} {d : RingInvolution B} {e : RingInvolution C}

/-- Adjoint for a specified coefficient involution, without a `Star` instance. -/
def adjoint (c : RingInvolution A) (M : Matrix ι ι A) : Matrix ι ι A :=
  (M.map c.bar).transpose

omit [Fintype ι] in
@[simp] theorem adjoint_one : adjoint c (1 : Matrix ι ι A) = 1 := by
  ext i j
  simp [adjoint, Matrix.one_apply, eq_comm]

omit [DecidableEq ι] in
theorem adjoint_mul (M N : Matrix ι ι A) :
    adjoint c (M * N) = adjoint c N * adjoint c M := by
  simp only [adjoint, Matrix.map_mul, Matrix.transpose_mul]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem adjoint_adjoint (M : Matrix ι ι A) : adjoint c (adjoint c M) = M := by
  ext i j
  exact c.bar_bar _

omit [Fintype ι] [DecidableEq ι] in
theorem adjoint_map (f : A →+* B) (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (M : Matrix ι ι A) : adjoint d (M.map f) = (adjoint c M).map f := by
  ext i j
  exact (hf _).symm

/-- A nonsingular Hermitian form retains its actual invertible Gram matrix. -/
structure Form (c : RingInvolution A) (ι : Type v) [Fintype ι] [DecidableEq ι] where
  gram : Matrix.GeneralLinearGroup ι A
  hermitian : adjoint c (gram : Matrix ι ι A) = (gram : Matrix ι ι A)

namespace Form

@[ext] theorem ext {H K : Form c ι} (h : H.gram = K.gram) : H = K := by
  cases H
  cases K
  cases h
  rfl

/-- Scalar extension of the actual Gram matrix. -/
def map (H : Form c ι) (f : A →+* B) (hf : ∀ a, f (c.bar a) = d.bar (f a)) :
    Form d ι where
  gram := Matrix.GeneralLinearGroup.map f H.gram
  hermitian := by
    change adjoint d ((H.gram : Matrix ι ι A).map f) = (H.gram : Matrix ι ι A).map f
    rw [adjoint_map f hf, H.hermitian]

@[simp] theorem map_gram (H : Form c ι) (f : A →+* B)
    (hf : ∀ a, f (c.bar a) = d.bar (f a)) :
    (H.map f hf).gram = Matrix.GeneralLinearGroup.map f H.gram := rfl

@[simp] theorem map_id (H : Form c ι) : H.map (RingHom.id A) (fun _ => rfl) = H := by
  apply ext
  rfl

theorem map_comp (H : Form c ι) (f : A →+* B) (g : B →+* C)
    (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hg : ∀ b, g (d.bar b) = e.bar (g b)) :
    (H.map f hf).map g hg = H.map (g.comp f) (fun a => by simpa only [RingHom.comp_apply] using (congrArg g (hf a)).trans (hg (f a))) := by
  apply ext
  rfl

end Form

/-- The full matrix preservation equation. -/
def Preserves (H : Form c ι) (M : Matrix ι ι A) : Prop :=
  adjoint c M * (H.gram : Matrix ι ι A) * M = (H.gram : Matrix ι ι A)

@[simp] theorem preserves_one (H : Form c ι) : Preserves H 1 := by simp [Preserves]

theorem preserves_mul {H : Form c ι} {M N : Matrix ι ι A}
    (hM : Preserves H M) (hN : Preserves H N) : Preserves H (M * N) := by
  unfold Preserves at *
  rw [adjoint_mul]
  calc
    _ = adjoint c N * (adjoint c M * (H.gram : Matrix ι ι A) * M) * N := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hM, hN]

theorem preserves_inv {H : Form c ι} (g : Matrix.GeneralLinearGroup ι A)
    (hg : Preserves H (g : Matrix ι ι A)) :
    Preserves H (g⁻¹ : Matrix.GeneralLinearGroup ι A) := by
  unfold Preserves at *
  calc
    _ = adjoint c (g⁻¹ : Matrix.GeneralLinearGroup ι A) *
        (adjoint c (g : Matrix ι ι A) * (H.gram : Matrix ι ι A) * (g : Matrix ι ι A)) *
        ((g⁻¹ : Matrix.GeneralLinearGroup ι A) : Matrix ι ι A) := by rw [hg]
    _ = adjoint c ((g * g⁻¹ : Matrix.GeneralLinearGroup ι A) : Matrix ι ι A) *
        (H.gram : Matrix ι ι A) * ((g * g⁻¹ : Matrix.GeneralLinearGroup ι A) : Matrix ι ι A) := by
      rw [Units.val_mul, adjoint_mul]
      simp only [Matrix.mul_assoc]
    _ = _ := by simp

/-- The actual general-linear subgroup preserving the Gram pairing. -/
def unitarySubgroup (H : Form c ι) : Subgroup (Matrix.GeneralLinearGroup ι A) where
  carrier := {g | Preserves H (g : Matrix ι ι A)}
  one_mem' := preserves_one H
  mul_mem' := preserves_mul
  inv_mem' hg := preserves_inv _ hg

/-- Actual determinant-one isometries. -/
def specialUnitarySubgroup (H : Form c ι) : Subgroup (Matrix.GeneralLinearGroup ι A) :=
  unitarySubgroup H ⊓ Matrix.GeneralLinearGroup.det.ker

@[simp] theorem mem_specialUnitarySubgroup (H : Form c ι) (g : Matrix.GeneralLinearGroup ι A) :
    g ∈ specialUnitarySubgroup H ↔
      adjoint c (g : Matrix ι ι A) * (H.gram : Matrix ι ι A) * (g : Matrix ι ι A) = H.gram ∧
        Matrix.GeneralLinearGroup.det g = 1 := Iff.rfl

variable {H : Form c ι} {J : Form d ι} {K : Form e ι}

theorem preserves_map (f : A →+* B) (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hJ : (H.gram : Matrix ι ι A).map f = J.gram)
    {M : Matrix ι ι A} (hM : Preserves H M) : Preserves J (M.map f) := by
  unfold Preserves at *
  rw [← hJ, adjoint_map f hf, ← Matrix.map_mul, ← Matrix.map_mul, hM]

/-- Coefficient change whenever the involutions and actual Gram matrices agree. -/
def coefficientMap (f : A →+* B) (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hJ : (H.gram : Matrix ι ι A).map f = J.gram) :
    specialUnitarySubgroup H →* specialUnitarySubgroup J where
  toFun g := ⟨Matrix.GeneralLinearGroup.map f g.1, preserves_map f hf hJ g.2.1, by
    change Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f g.1) = 1
    rw [Matrix.GeneralLinearGroup.map_det, g.2.2, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ _ _)

@[simp] theorem coefficientMap_val (f : A →+* B)
    (hf : ∀ a, f (c.bar a) = d.bar (f a))
    (hJ : (H.gram : Matrix ι ι A).map f = J.gram) (g : specialUnitarySubgroup H) :
    ((coefficientMap f hf hJ g).1 : Matrix ι ι B) = (g.1 : Matrix ι ι A).map f := rfl

@[simp] theorem coefficientMap_id (g : specialUnitarySubgroup H) :
    coefficientMap (RingHom.id A) (fun _ => rfl) (H := H) (J := H) rfl g = g := by
  apply Subtype.ext
  rfl

theorem coefficientMap_comp (f : A →+* B) (g : B →+* C)
    (hf : ∀ a, f (c.bar a) = d.bar (f a)) (hg : ∀ b, g (d.bar b) = e.bar (g b))
    (hJ : (H.gram : Matrix ι ι A).map f = J.gram)
    (hK : (J.gram : Matrix ι ι B).map g = K.gram) (x : specialUnitarySubgroup H) :
    coefficientMap g hg hK (coefficientMap f hf hJ x) =
      coefficientMap (g.comp f) (fun a => by simpa only [RingHom.comp_apply] using (congrArg g (hf a)).trans (hg (f a)))
        (by rw [← hK, ← hJ]; rfl) x := by
  apply Subtype.ext
  rfl

end Langlands.GroupScheme.HermitianMatrix
