import Langlands.GroupScheme.Dynamic.GeneralLinearCocharacterDiagonal
import Langlands.GroupScheme.Torus.ExponentCharacters
import Langlands.GroupScheme.Lie.AffineCoordinates
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # A faithful representation with one opposite pair of weights has rank at most one -/

noncomputable section
universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.GeneralLinear.CocharacterDiagonal

variable {K : Type u} [Field K] {n : Type} [Fintype n] [DecidableEq n]

/-- Every column of an invertible matrix is nonzero. -/
theorem column_ne_zero (B : GL n K) (j : n) : (B : Matrix n n K).col j ≠ 0 := by
  intro h
  have he := congrArg (fun M : Matrix n n K => M j j) B.inv_val
  have hz (r : n) : (B : Matrix n n K) r j = 0 := congrFun h r
  simp [Matrix.mul_apply, hz] at he

variable (I : Type u) [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
/-- The columns of a diagonalizing matrix are weight vectors at rational points. -/
theorem column_weight_of_diagonalization
    (ρ : MatrixRepresentation (splitTorus (Spec (CommRingCat.of K)) I) n)
    (B : GL n K) (w : n → (I → ℤ))
    (h : ∀ t : I → Kˣ, B⁻¹ * matrixAt I ρ t * B =
      diagonalMatrix (fun j => splitTorus.exponentValue I t (Multiplicative.ofAdd (w j))))
    (j : n) (t : I → Kˣ) :
    (matrixAt I ρ t : Matrix n n K) *ᵥ (B : Matrix n n K).col j =
      (splitTorus.exponentValue I t (Multiplicative.ofAdd (w j)) : K) •
        (B : Matrix n n K).col j := by
  have he := congrArg (fun M : GL n K => B * M) (h t)
  simp only [← mul_assoc, mul_inv_cancel, one_mul] at he
  have hm : (matrixAt I ρ t : Matrix n n K) * (B : Matrix n n K) =
      (B : Matrix n n K) * Matrix.diagonal
        (fun j => (splitTorus.exponentValue I t (Multiplicative.ofAdd (w j)) : K)) :=
    congrArg Units.val he
  funext r
  have hr := congrFun (congrFun hm r) j
  rw [Matrix.mul_diagonal] at hr
  simpa only [Units.val_mul, coe_diagonalMatrix, Matrix.mul_diagonal,
    Matrix.mul_apply, Matrix.col_apply, Matrix.mulVec, dotProduct, Pi.smul_apply,
    smul_eq_mul, mul_comm] using hr

/-- The sign of a weight known to lie in zero and a fixed opposite pair. -/
def weightSign (w : n → (I → ℤ)) (m : I → ℤ) (j : n) : ℤ :=
  if w j = 0 then 0 else if w j = m then 1 else -1

omit [Fintype n] [DecidableEq n] [DecidableEq I] in
/-- A trichotomy of weights expresses each weight as its sign times the fixed weight. -/
theorem weight_eq_sign_smul (w : n → (I → ℤ)) (m : I → ℤ)
    (hw : ∀ j, w j = 0 ∨ w j = m ∨ w j = -m) (j : n) :
    w j = weightSign I w m j • m := by
  rcases hw j with h | h | h
  · simp [weightSign, h]
  · by_cases hm : m = 0
    · simp [weightSign, h, hm]
    · simp [weightSign, h, hm]
  · by_cases hm : m = 0
    · simp [weightSign, h, hm]
    · by_cases he : -m = m
      · simp [weightSign, h, hm, he]
      · simp [weightSign, h, hm, he]

omit [DecidableEq I] in
/-- Scalar multiplication of an exponent corresponds to an integer power of its value. -/
theorem exponentValue_zsmul {A : Type u} [CommRing A] [Algebra K A]
    (t : I → Aˣ) (m : I → ℤ) (e : ℤ) :
    splitTorus.exponentValue I t (Multiplicative.ofAdd (e • m)) =
      splitTorus.exponentValue I t (Multiplicative.ofAdd m) ^ e := by
  change splitTorus.exponentValue I t ((Multiplicative.ofAdd m) ^ e) = _
  exact map_zpow _ _ _

omit [DecidableEq I] in
/-- With only zero and one opposite pair of weights, diagonalization factors through one character. -/
theorem factor_through_exponentCharacter
    (ρ : MatrixRepresentation (splitTorus (Spec (CommRingCat.of K)) I) n)
    (B : GL n K) (w : n → (I → ℤ)) (m : I → ℤ)
    (hw : ∀ j, w j = 0 ∨ w j = m ∨ w j = -m)
    (hB : ∀ (A : Type u) [CommRing A] [Algebra K A] (t : I → Aˣ),
      (Matrix.GeneralLinearGroup.map (algebraMap K A) B)⁻¹ * matrixAt I ρ t *
        Matrix.GeneralLinearGroup.map (algebraMap K A) B =
      diagonalMatrix (fun j => splitTorus.exponentValue I t (Multiplicative.ofAdd (w j)))) :
    ρ ≫ ((GeneralLinear.groupScheme n (CommRingCat.of K)).innerIso
      (rationalMatrixPoint B⁻¹)).hom =
    CommGroupScheme.groupHom (splitTorus.exponentCharacter (Spec (CommRingCat.of K)) I m) ≫
      GeneralLinear.diagonalCocharacter n (CommRingCat.of K) (weightSign I w m) := by
  let : IsAffineHom (splitTorus (Spec (CommRingCat.of K)) I).X.hom :=
    isAffineHom_splitTorus_spec (CommRingCat.of K) I
  apply Grp.hom_ext
  apply (cancel_epi (Lie.coordinateIso (splitTorus (Spec (CommRingCat.of K)) I)).hom).mp
  let A := Lie.coordinateAlgebra (splitTorus (Spec (CommRingCat.of K)) I)
  let x : (algSpec (CommRingCat.of K)).obj (op A) ⟶
      (splitTorus (Spec (CommRingCat.of K)) I).X :=
    (Lie.coordinateIso (splitTorus (Spec (CommRingCat.of K)) I)).hom
  let t := splitTorus.algebraPointsEquiv I A x
  apply (GeneralLinear.affinePointsEquiv n (CommRingCat.of K) A).injective
  change GeneralLinear.affinePointsEquiv n (CommRingCat.of K) A
    ((x ≫ ρ.hom.hom) ≫ ((GeneralLinear.groupScheme n (CommRingCat.of K)).innerIso
      (rationalMatrixPoint B⁻¹)).hom.hom.hom) =
    GeneralLinear.affinePointsEquiv n (CommRingCat.of K) A
      ((x ≫ (CommGroupScheme.groupHom
        (splitTorus.exponentCharacter (Spec (CommRingCat.of K)) I m)).hom.hom) ≫
        (GeneralLinear.diagonalCocharacter n (CommRingCat.of K) (weightSign I w m)).hom.hom)
  rw [comp_innerIso_hom, map_mul, map_mul, map_inv,
    affinePointsEquiv_constant_rationalMatrixPoint, affinePointsEquiv_diagonalCocharacter]
  simp only [map_inv, inv_inv]
  have he := hB A t
  have hm : matrixAt I ρ t = GeneralLinear.affinePointsEquiv n (CommRingCat.of K) A
      (x ≫ ρ.hom.hom) := by
    dsimp only [matrixAt, t]
    rw [MulEquiv.symm_apply_apply]
    rfl
  rw [hm] at he
  erw [he]
  have hc : Gm.affinePointsEquiv ((algSpec (CommRingCat.of K)).obj (op A)).hom
      (x ≫ (CommGroupScheme.groupHom
        (splitTorus.exponentCharacter (Spec (CommRingCat.of K)) I m)).hom.hom) =
      splitTorus.exponentValue I t (Multiplicative.ofAdd m) :=
    splitTorus.characterValue_exponentCharacter I m x
  rw [hc]
  apply Units.ext
  ext a j
  simp only [coe_diagonalMatrix, GeneralLinear.coe_diagonalUnits]
  congr 1
  funext j
  rw [weight_eq_sign_smul I w m hw j, exponentValue_zsmul (K := K)]

omit [DecidableEq I] in
/-- A mono representation whose weights lie in one opposite pair has at most one torus factor. -/
theorem card_le_one_of_weight_trichotomy
    (ρ : MatrixRepresentation (splitTorus (Spec (CommRingCat.of K)) I) n)
    [Mono ρ.hom.hom]
    (B : GL n K) (w : n → (I → ℤ)) (m : I → ℤ)
    (hw : ∀ j, w j = 0 ∨ w j = m ∨ w j = -m)
    (hB : ∀ (A : Type u) [CommRing A] [Algebra K A] (t : I → Aˣ),
      (Matrix.GeneralLinearGroup.map (algebraMap K A) B)⁻¹ * matrixAt I ρ t *
        Matrix.GeneralLinearGroup.map (algebraMap K A) B =
      diagonalMatrix (fun j => splitTorus.exponentValue I t (Multiplicative.ofAdd (w j)))) :
    Nat.card I ≤ 1 := by
  let χ := CommGroupScheme.groupHom
    (splitTorus.exponentCharacter (Spec (CommRingCat.of K)) I m)
  let d := GeneralLinear.diagonalCocharacter n (CommRingCat.of K) (weightSign I w m)
  have he : χ ≫ d = ρ ≫ ((GeneralLinear.groupScheme n (CommRingCat.of K)).innerIso
      (rationalMatrixPoint B⁻¹)).hom := (factor_through_exponentCharacter I ρ B w m hw hB).symm
  have : Mono (χ.hom.hom ≫ d.hom.hom) := by
    change Mono (χ ≫ d).hom.hom
    rw [he]
    change Mono (ρ.hom.hom ≫ _)
    have : IsIso ((GeneralLinear.groupScheme n (CommRingCat.of K)).innerIso
      (rationalMatrixPoint B⁻¹)).hom.hom.hom := (Grp.forget _).map_isIso
        ((GeneralLinear.groupScheme n (CommRingCat.of K)).innerIso (rationalMatrixPoint B⁻¹)).hom
    infer_instance
  have : Mono χ.hom.hom := mono_of_mono _ d.hom.hom
  have : IsIso (splitTorus.gmIso (Spec (CommRingCat.of K))).hom.hom.hom :=
    (Grp.forget _).map_isIso (splitTorus.gmIso (Spec (CommRingCat.of K))).hom
  have : Mono (χ ≫ (splitTorus.gmIso (Spec (CommRingCat.of K))).hom).hom.hom := by
    change Mono (χ.hom.hom ≫ _)
    infer_instance
  simpa using splitTorus.card_le_card_of_mono I PUnit
    (χ ≫ (splitTorus.gmIso (Spec (CommRingCat.of K))).hom)

end Langlands.GroupScheme.GeneralLinear.CocharacterDiagonal
