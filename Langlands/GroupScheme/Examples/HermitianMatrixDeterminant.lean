import Langlands.GroupScheme.Examples.HermitianMatrixGroupScheme
import Langlands.GroupScheme.Examples.HermitianMatrixNondegenerate
import Langlands.GroupScheme.Examples.HermitianNondegenerateCoordinates
import Langlands.GroupScheme.Examples.HermitianHyperbolicGramCoordinates
import Langlands.GroupScheme.Rational.GeneralLinearCharacterMatrices

/-! # Determinants of Hermitian isometries over a quadratic field -/

noncomputable section

universe u

open Matrix

namespace Langlands.GroupScheme.HermitianMatrix

open SU3Root Module

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

section Adjoint

variable {A : Type u} [CommRing A] {n : ℕ} (c : RingInvolution A)

/-- The order-reversing adjoint on invertible matrices. -/
def adjointUnit (g : GL (Fin n) A) : GL (Fin n) A where
  val := adjoint c (g : Matrix (Fin n) (Fin n) A)
  inv := adjoint c ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)
  val_inv := by rw [← adjoint_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, adjoint_one]
  inv_val := by rw [← adjoint_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, adjoint_one]

@[simp] theorem adjointUnit_val (g : GL (Fin n) A) :
    (adjointUnit c g : Matrix (Fin n) (Fin n) A) = adjoint c (g : Matrix (Fin n) (Fin n) A) := rfl

@[simp] theorem adjointUnit_inv (g : GL (Fin n) A) : adjointUnit c g⁻¹ = (adjointUnit c g)⁻¹ :=
  Units.ext rfl

@[simp] theorem adjointUnit_mul (g h : GL (Fin n) A) :
    adjointUnit c (g * h) = adjointUnit c h * adjointUnit c g := by
  apply Units.ext
  exact adjoint_mul _ _

@[simp] theorem adjointUnit_adjointUnit (g : GL (Fin n) A) : adjointUnit c (adjointUnit c g) = g :=
  Units.ext (adjoint_adjoint _)

variable {c}

/-- The inverse of a nonsingular Hermitian Gram matrix is Hermitian. -/
def Form.inverse (H : Form c (Fin n)) : Form c (Fin n) where
  gram := H.gram⁻¹
  hermitian := by
    have h : adjointUnit c H.gram = H.gram := Units.ext H.hermitian
    exact congrArg Units.val ((adjointUnit_inv c H.gram).trans (congrArg Inv.inv h))

private theorem mul_inv_iff (a x b : GL (Fin n) A) :
    a * x * b = x ↔ b * x⁻¹ * a = x⁻¹ := by
  constructor
  · intro h
    calc
      _ = b * (a * x * b)⁻¹ * a := by rw [h]
      _ = _ := by group
  · intro h
    calc
      _ = a * (b * x⁻¹ * a)⁻¹ * b := by rw [h, inv_inv]
      _ = _ := by group

/-- The column isometry condition is the row isometry condition for the inverse Gram matrix. -/
theorem preserves_iff_row_inverse (H : Form c (Fin n)) (g : GL (Fin n) A) :
    Preserves H (g : Matrix (Fin n) (Fin n) A) ↔
      (g : Matrix (Fin n) (Fin n) A) * (H.inverse.gram : Matrix (Fin n) (Fin n) A) *
        adjoint c (g : Matrix (Fin n) (Fin n) A) = H.inverse.gram := by
  change ((adjointUnit c g * H.gram * g : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = H.gram ↔
    ((g * H.gram⁻¹ * adjointUnit c g : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = H.gram⁻¹
  exact Units.val_injective.eq_iff.trans ((mul_inv_iff (adjointUnit c g) H.gram g).trans
    Units.val_injective.eq_iff.symm)

/-- The determinant of a Hermitian isometry has conjugate norm one. -/
theorem bar_det_mul_det_eq_one (H : Form c (Fin n)) (g : GL (Fin n) A)
    (hg : Preserves H (g : Matrix (Fin n) (Fin n) A)) :
    c.bar (GeneralLinearGroup.det g : A) * (GeneralLinearGroup.det g : A) = 1 := by
  have h : (adjointUnit c g) * H.gram * g = H.gram := Units.ext hg
  have hd := congrArg GeneralLinearGroup.det h
  simp only [map_mul] at hd
  rw [mul_right_comm] at hd
  have hd' : GeneralLinearGroup.det (adjointUnit c g) * GeneralLinearGroup.det g = 1 :=
    mul_right_cancel (hd.trans (one_mul _).symm)
  have hbar : (GeneralLinearGroup.det (adjointUnit c g) : A) = c.bar (GeneralLinearGroup.det g : A) :=
    det_adjoint _
  simpa only [Units.val_mul, hbar, Units.val_one] using congrArg Units.val hd'

end Adjoint

/-- Every scalar of conjugate norm one is the determinant of a Hermitian isometry in
positive dimension over a separable quadratic extension. -/
theorem exists_unitary_det_eq {F E : Type u} [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    {n : ℕ} (hn : 0 < n) (H : Form (fieldInvolution F E) (Fin n)) (a : Eˣ)
    (ha : (fieldInvolution F E).bar (a : E) * (a : E) = 1) :
    ∃ g : GL (Fin n) E, Preserves H (g : Matrix (Fin n) (Fin n) E) ∧ GeneralLinearGroup.det g = a := by
  classical
  let c := fieldInvolution F E
  obtain ⟨b₀, hb₀, _⟩ := HermitianRoot.exists_orthogonal_basis_of_separatingLeft
    H.linearFirst H.bar_linearFirst H.eq_zero_of_pairing_right
  have hd : finrank E (Fin n → E) = n := by simp
  let f := finCongr hd
  let b := b₀.reindex f
  let P := HermitianRoot.MultiHyperbolic.coordinateMatrix b.equivFun.symm
  let D := adjointUnit c P * H.gram * P
  have hH : adjointUnit c H.gram = H.gram := Units.ext H.hermitian
  have hD : adjointUnit c D = D := by simp only [D, adjointUnit_mul, adjointUnit_adjointUnit, hH, mul_assoc]
  let J : Form c (Fin n) := ⟨D, congrArg Units.val hD⟩
  have hP : adjoint c (P : Matrix (Fin n) (Fin n) E) * (H.gram : Matrix (Fin n) (Fin n) E) *
      (P : Matrix (Fin n) (Fin n) E) = J.gram := rfl
  have hJ : (J.gram : Matrix (Fin n) (Fin n) E) = diagonal (fun i => J.gram i i) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · rw [diagonal_apply_ne _ hij, ← hP]
      change (((P : Matrix (Fin n) (Fin n) E).map c.bar).transpose *
        (H.gram : Matrix (Fin n) (Fin n) E) * (P : Matrix (Fin n) (Fin n) E)) i j = 0
      rw [HermitianRoot.MultiHyperbolic.coordinateMatrix_congruence_apply,
        ← H.pairing_eq_dotProduct, Basis.equivFun_symm_single, Basis.equivFun_symm_single]
      have hne : f.symm j ≠ f.symm i := fun h => hij (f.symm.injective h).symm
      have ho := hb₀ hne
      simpa only [b, Basis.reindex_apply, Form.linearFirst_apply] using ho
  let i₀ : Fin n := ⟨0, hn⟩
  let w : Fin n → Eˣ := Pi.mulSingle i₀ a
  let z := GeneralLinear.diagonalMatrixUnits E w
  have hz : Preserves J (z : Matrix (Fin n) (Fin n) E) := by
    have hbar : adjoint c (z : Matrix (Fin n) (Fin n) E) = diagonal (fun i => c.bar (w i : E)) := by
      rw [GeneralLinear.diagonalMatrixUnits_val, adjoint, Matrix.diagonal_map (map_zero _), diagonal_transpose]
    unfold Preserves
    rw [hbar, GeneralLinear.diagonalMatrixUnits_val, hJ, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : i = i₀
    · subst i
      change c.bar (w i₀ : E) * J.gram i₀ i₀ * (w i₀ : E) = _
      rw [mul_right_comm]
      have hw : w i₀ = a := Pi.mulSingle_eq_same _ _
      rw [hw, ha, one_mul]
    · have hw : w i = 1 := Pi.mulSingle_eq_of_ne hi _
      simp [hw]
  have hzdet : GeneralLinearGroup.det z = a := by
    apply Units.ext
    change (z : Matrix (Fin n) (Fin n) E).det = (a : E)
    rw [GeneralLinear.diagonalMatrixUnits_val, det_diagonal]
    simp [w, Pi.mulSingle, Function.update_apply, apply_ite (fun t : Eˣ => (t : E))]
  refine ⟨P * z * P⁻¹, preserves_isometry_conj P hP z hz, ?_⟩
  rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul, hzdet]

/-- Hermitian isometries in positive dimension attain every conjugate-norm-one unit
of the underlying separable quadratic extension as a determinant. -/
def UnitaryDeterminantSurjectivityStatement : Prop :=
  ∀ (F E : Type u) [Field F] [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    (n : ℕ), 0 < n → ∀ (H : Form (fieldInvolution F E) (Fin n)) (a : Eˣ),
      (fieldInvolution F E).bar (a : E) * (a : E) = 1 →
      ∃ g : GL (Fin n) E,
        Preserves H (g : Matrix (Fin n) (Fin n) E) ∧ GeneralLinearGroup.det g = a

end Langlands.GroupScheme.HermitianMatrix
