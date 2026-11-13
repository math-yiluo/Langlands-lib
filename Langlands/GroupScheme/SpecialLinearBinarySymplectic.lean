import Langlands.GroupScheme.SymplecticMatrix.SimplyConnected
import Langlands.GroupScheme.SpecialLinear

/-! # The binary symplectic group is the binary special linear group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.SpecialLinear.BinarySymplectic

section Matrices

variable {A : Type*} [CommRing A]

/-- The coordinates `Fin 1 ⊕ Fin 1` of the binary symplectic group, indexed by `Fin 2`. -/
abbrev indexEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2 := finSumFinEquiv

/-- The determinant of a binary matrix in symplectic coordinates. -/
theorem det_eq (g : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) A) :
    g.det = g (.inl 0) (.inl 0) * g (.inr 0) (.inr 0) -
      g (.inl 0) (.inr 0) * g (.inr 0) (.inl 0) := by
  rw [← Matrix.det_reindex_self indexEquiv g, Matrix.det_fin_two]
  rfl

/-- For binary matrices, `g J gᵀ = det g • J`. -/
theorem mul_J_mul_transpose (g : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) A) :
    g * Matrix.J (Fin 1) A * gᵀ = g.det • Matrix.J (Fin 1) A := by
  rw [det_eq]
  ext (i | i) (j | j) <;>
    obtain rfl : i = 0 := Subsingleton.elim _ _ <;>
    obtain rfl : j = 0 := Subsingleton.elim _ _ <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.J] <;> ring

/-- A binary matrix is symplectic exactly when its determinant is one. -/
theorem mem_symplecticGroup_iff (g : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) A) :
    g ∈ Matrix.symplecticGroup (Fin 1) A ↔ g.det = 1 := by
  rw [SymplecticGroup.mem_iff, mul_J_mul_transpose]
  constructor
  · intro h
    have h' := congrFun (congrFun h (.inl 0)) (.inr 0)
    simp [Matrix.J] at h'
    exact h'
  · intro h
    rw [h, one_smul]

/-- Reindexing by `Fin 1 ⊕ Fin 1 ≃ Fin 2` identifies binary symplectic matrices with
determinant-one `2 × 2` matrices. -/
def toSpecialLinear :
    Matrix.symplecticGroup (Fin 1) A ≃* Matrix.SpecialLinearGroup (Fin 2) A where
  toFun g := ⟨Matrix.reindex indexEquiv indexEquiv (g : Matrix (Fin 1 ⊕ Fin 1) _ A), by
    rw [Matrix.det_reindex_self]
    exact (mem_symplecticGroup_iff _).1 g.2⟩
  invFun g := ⟨Matrix.reindex indexEquiv.symm indexEquiv.symm (g : Matrix (Fin 2) (Fin 2) A),
    (mem_symplecticGroup_iff _).2 (by rw [Matrix.det_reindex_self]; exact g.2)⟩
  left_inv g := by
    apply Subtype.ext
    simp
  right_inv g := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp
  map_mul' g h := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    change Matrix.reindex indexEquiv indexEquiv
        ((g : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) A) *
          (h : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) A)) i j =
      (Matrix.reindex indexEquiv indexEquiv (g : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) A) *
        Matrix.reindex indexEquiv indexEquiv (h : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) A)) i j
    rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
      Matrix.submatrix_mul_equiv]

@[simp] theorem coe_toSpecialLinear (g : Matrix.symplecticGroup (Fin 1) A) :
    ((toSpecialLinear g : Matrix.SpecialLinearGroup (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      Matrix.reindex indexEquiv indexEquiv (g : Matrix (Fin 1 ⊕ Fin 1) _ A) :=
  rfl

/-- The identification commutes with entrywise coefficient change. -/
theorem toSpecialLinear_map {B : Type*} [CommRing B] (f : A →+* B)
    (g : Matrix.symplecticGroup (Fin 1) A) :
    toSpecialLinear (SymplecticMatrix.map (Fin 1) f g) =
      Matrix.SpecialLinearGroup.map f (toSpecialLinear g) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rfl

end Matrices

section Scheme

variable (R : CommRingCat.{u})

/-- Points of the binary symplectic group scheme, as determinant-one `2 × 2` matrices. -/
def symplecticPointsEquiv (T : Over (Spec R)) :
    (T ⟶ (SymplecticMatrix.groupScheme (Fin 1) R).X) ≃*
      Matrix.SpecialLinearGroup (Fin 2) Γ(T.left, ⊤) :=
  (SymplecticMatrix.pointsEquiv (Fin 1) R T).trans toSpecialLinear

theorem symplecticPointsEquiv_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (SymplecticMatrix.groupScheme (Fin 1) R).X) :
    symplecticPointsEquiv R T' (a ≫ x) =
      Matrix.SpecialLinearGroup.map a.left.appTop.hom (symplecticPointsEquiv R T x) := by
  simp only [symplecticPointsEquiv, MulEquiv.trans_apply,
    SymplecticMatrix.pointsEquiv_naturality, toSpecialLinear_map]

/-- **`Sp_2 = SL_2`.** The binary symplectic group scheme is the binary special linear group
scheme, by reindexing coordinates along `Fin 1 ⊕ Fin 1 ≃ Fin 2`. -/
def symplecticIso :
    SymplecticMatrix.groupScheme (Fin 1) R ≅ SpecialLinear.groupScheme (Fin 2) R :=
  isoOfPointModels (fun T => Matrix.SpecialLinearGroup (Fin 2) Γ(T.left, ⊤))
    (fun a => Matrix.SpecialLinearGroup.map a.left.appTop.hom)
    (symplecticPointsEquiv R)
    (SpecialLinear.pointsEquiv (Fin 2) R)
    (symplecticPointsEquiv_naturality R)
    (fun {_ _} a y => SpecialLinear.pointsEquiv_naturality a y)

end Scheme

/-- **Simple connectedness of `SL_2`.** The binary special linear group over a field is
simply connected, by transport of the simple connectedness of `Sp_2` along `symplecticIso`. -/
theorem isSimplyConnected (k : Type u) [Field k] :
    IsSimplyConnected (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of k)) :=
  IsSimplyConnected.of_iso (symplecticIso (CommRingCat.of k)).symm
    (SymplecticMatrix.isSimplyConnected (Fin 1) k)

end Langlands.GroupScheme.SpecialLinear.BinarySymplectic
