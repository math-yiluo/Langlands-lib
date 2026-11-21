import Langlands.GroupScheme.Quaternionic.QuaternionicSplitScalarGram
import Langlands.LinearAlgebra.OppositeBinarySubforms
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! # Opposite invertible skew values in a split quaternion chart -/

noncomputable section

universe u v w z k

open Matrix Langlands.SymmetricBilinear

namespace Langlands.GroupScheme.Quaternionic

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000

variable {R : Type u} {A : Type v} [Field R] [Ring A] [Algebra R A]
  {I : Type w} [Fintype I] [DecidableEq I]
  (e : A ≃ₐ[R] Matrix (Fin 2) (Fin 2) R) (τ : FirstKindInvolution R A)
  (hτ : ∀ a : A, e (τ a) * FirstKindInvolution.gramTwo R =
    FirstKindInvolution.gramTwo R * (e a)ᵀ)

local notation "J" => FirstKindInvolution.gramTwo R

include hτ in
theorem splitSkewScalarGram_pairing (H : Matrix I I A) (x y : I → A) (a b : Fin 2) :
    (splitSkewScalarGram e H).toBilin' (splitSkewRows e x a) (splitSkewRows e y b) =
      (e (τ.matrixSesqBilin H x y) * J) a b := by
  rw [matrixSesqBilin_splitSkewScalarGram e τ hτ, Matrix.toBilin'_apply', Matrix.dotProduct_mulVec]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.vecMul, dotProduct]

include hτ in
private theorem splitSkewValue_diagonal (H : Matrix I I A) (hH : τ.matrix I H = -H)
    (x y : I × Fin 2 → R)
    (hxy : (splitSkewScalarGram e H).toBilin' x y = 0) :
    let B := (splitSkewScalarGram e H).toBilin'
    let X : Matrix (Fin 2) (I × Fin 2) R := Matrix.of ![x, y]
    let r := fromSplitSkewRows e X
    e (τ.matrixSesqBilin H r r) * J = Matrix.diagonal ![B x x, B y y] := by
  intro B X r
  have hsym := Matrix.isSymm_toBilin'_iff_isSymm.mpr (splitSkewScalarGram_isSymm e τ hτ hH)
  have hyx : B y x = 0 := (hsym.eq y x).trans hxy
  have hpair (a b : Fin 2) : B (splitSkewRows e r a) (splitSkewRows e r b) =
      (e (τ.matrixSesqBilin H r r) * J) a b := splitSkewScalarGram_pairing e τ hτ H r r a b
  ext a b
  rw [← hpair, show splitSkewRows e r = X from splitSkewRows_fromSplitSkewRows e X]
  change B (![x, y] a) (![x, y] b) = Matrix.diagonal ![B x x, B y y] a b
  fin_cases a <;> fin_cases b <;> simp [hxy, hyx, B]

private theorem finrank_splitRows_ge_two (R : Type u) [Field R] (K : Type k)
    [Fintype K] [Nonempty K] : 2 ≤ Module.finrank R (K × Fin 2 → R) := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin]
  have := Fintype.card_pos (α := K)
  omega

variable {L : Type z} [Fintype L] [DecidableEq L]

include hτ in
/-- A normalized isotropic row for the sum guarantees opposite invertible skew
  values in the two blocks when the quaternion coefficients split. -/
theorem splitSkew_exists_opposite_unit_values (h2 : (2 : R) ≠ 0)
    [Nonempty I] [Nonempty L] {H : Matrix I I A} {G : Matrix L L A}
    (hH : τ.matrix I H = -H) (hG : τ.matrix L G = -G) (huH : IsUnit H) (huG : IsUnit G)
    (x y : I → A) (a b : L → A)
    (hzero : τ.matrixSesqBilin H x x + τ.matrixSesqBilin G a a = 0)
    (hone : τ.matrixSesqBilin H x y + τ.matrixSesqBilin G a b = 1) :
    ∃ (r : I → A) (s : L → A), IsUnit (-(τ.matrixSesqBilin G s s)) ∧
      τ.matrixSesqBilin H r r = -(τ.matrixSesqBilin G s s) := by
  let B := (splitSkewScalarGram e H).toBilin'
  let C := (splitSkewScalarGram e G).toBilin'
  let T := orthogonalSum B C
  let U (r : I → A) (s : L → A) (i : Fin 2) := (splitSkewRows e r i, splitSkewRows e s i)
  have hpair (r r' : I → A) (s s' : L → A) (i j : Fin 2) :
      T (U r s i) (U r' s' j) =
        (e (τ.matrixSesqBilin H r r' + τ.matrixSesqBilin G s s') * J) i j := by
    simp only [T, U, B, C, orthogonalSum_apply, splitSkewScalarGram_pairing e τ hτ,
      map_add, add_mul, Matrix.add_apply]
  have hxx (i j : Fin 2) : T (U x a i) (U x a j) = 0 := by
    rw [hpair, hzero, map_zero, zero_mul, Matrix.zero_apply]
  have hxy (i j : Fin 2) : T (U x a i) (U y b j) = J i j := by
    rw [hpair, hone, map_one, one_mul]
  have hli : LinearIndependent R ![U x a 0, U x a 1] := by
    apply LinearIndependent.pair_iff.mpr
    intro c d h
    have hz (j : Fin 2) : c * J 0 j + d * J 1 j = 0 := by
      have hc := congrArg (fun f => T f (U y b j)) h
      simpa only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, hxy, map_zero, LinearMap.zero_apply] using hc
    exact ⟨by simpa [FirstKindInvolution.gramTwo] using hz 1,
      by simpa [FirstKindInvolution.gramTwo] using hz 0⟩
  have hB : B.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr (splitSkewScalarGram_isSymm e τ hτ hH)
  have hC : C.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr (splitSkewScalarGram_isSymm e τ hτ hG)
  have hBnd : B.Nondegenerate := LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr
    (((splitSkewScalarGram e H).isUnit_iff_isUnit_det.mp (splitSkewScalarGram_isUnit e huH)).ne_zero)
  have hCnd : C.Nondegenerate := LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr
    (((splitSkewScalarGram e G).isUnit_iff_isUnit_det.mp (splitSkewScalarGram_isUnit e huG)).ne_zero)
  obtain ⟨r₁, r₂, s₁, s₂, hr₁, hr₂, hr, hs, h₁, h₂⟩ :=
    oppositeBinarySubforms R h2 _ _ B C hB hC hBnd hCnd
      (finrank_splitRows_ge_two R I) (finrank_splitRows_ge_two R L)
      _ _ hli (hxx 0 0) (hxx 0 1) (hxx 1 1)
  let r := fromSplitSkewRows e (Matrix.of ![r₁, r₂])
  let s := fromSplitSkewRows e (Matrix.of ![s₁, s₂])
  have hd₁ : e (τ.matrixSesqBilin H r r) * J = Matrix.diagonal ![B r₁ r₁, B r₂ r₂] :=
    splitSkewValue_diagonal e τ hτ H hH r₁ r₂ hr
  have hd₂ : e (τ.matrixSesqBilin G s s) * J = Matrix.diagonal ![C s₁ s₁, C s₂ s₂] :=
    splitSkewValue_diagonal e τ hτ G hG s₁ s₂ hs
  have hJ : IsUnit (J : Matrix (Fin 2) (Fin 2) R) := FirstKindInvolution.isUnit_gramTwo
  have hD : IsUnit (e (τ.matrixSesqBilin H r r) * J) := by
    rw [hd₁, Matrix.isUnit_diagonal, Pi.isUnit_iff]
    intro i
    fin_cases i
    · exact isUnit_iff_ne_zero.mpr hr₁
    · exact isUnit_iff_ne_zero.mpr hr₂
  have hvalue : IsUnit (τ.matrixSesqBilin H r r) := by
    have h := hD.mul (hJ.unit⁻¹).isUnit
    rw [mul_assoc, hJ.mul_val_inv, mul_one] at h
    simpa only [AlgEquiv.symm_apply_apply] using h.map e.symm
  have hsum : (e (τ.matrixSesqBilin H r r) + e (τ.matrixSesqBilin G s s)) * J = 0 := by
    rw [add_mul, hd₁, hd₂]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.add_apply, h₁, h₂]
  have hneg : τ.matrixSesqBilin H r r = -(τ.matrixSesqBilin G s s) := by
    apply eq_neg_of_add_eq_zero_left
    apply e.injective
    rw [map_add, map_zero]
    have h := congrArg (· * (↑hJ.unit⁻¹ : Matrix (Fin 2) (Fin 2) R)) hsum
    simpa only [mul_assoc, hJ.mul_val_inv, mul_one, zero_mul] using h
  exact ⟨r, s, hneg ▸ hvalue, hneg⟩

/-- A normalized isotropic row in an orthogonal sum over split quaternion
  coefficients yields opposite invertible skew values in the two blocks. -/
def QuaternionicSplitOppositeValuesStatement : Prop :=
  ∀ (R : Type u) (A : Type v) [Field R] [Ring A] [Algebra R A], (2 : R) ≠ 0 →
    ∀ (e : A ≃ₐ[R] Matrix (Fin 2) (Fin 2) R) (τ : FirstKindInvolution R A),
    (∀ a : A, e (τ a) * FirstKindInvolution.gramTwo R =
      FirstKindInvolution.gramTwo R * (e a)ᵀ) →
    ∀ (I : Type w) (L : Type z) [Fintype I] [DecidableEq I] [Nonempty I]
      [Fintype L] [DecidableEq L] [Nonempty L]
      (H : Matrix I I A) (G : Matrix L L A),
      τ.matrix I H = -H → τ.matrix L G = -G → IsUnit H → IsUnit G →
      ∀ (x y : I → A) (a b : L → A),
        τ.matrixSesqBilin H x x + τ.matrixSesqBilin G a a = 0 →
        τ.matrixSesqBilin H x y + τ.matrixSesqBilin G a b = 1 →
        ∃ (r : I → A) (s : L → A), IsUnit (-(τ.matrixSesqBilin G s s)) ∧
          τ.matrixSesqBilin H r r = -(τ.matrixSesqBilin G s s)

theorem quaternionicSplitOppositeValues : QuaternionicSplitOppositeValuesStatement.{u, v, w, z} := by
  intro R A _ _ _ h2 e τ hτ I L _ _ _ _ _ _ H G hH hG huH huG x y a b hx hxy
  exact splitSkew_exists_opposite_unit_values e τ hτ h2 hH hG huH huG x y a b hx hxy

end Langlands.GroupScheme.Quaternionic
