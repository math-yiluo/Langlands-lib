import Langlands.Representation.Conductor.SphericalPolynomial

/-! # Central torus shifts of the actual spherical formula -/

noncomputable section

namespace Langlands.Conductor

open MvPolynomial Langlands.GeneralLinear Langlands.GeneralLinear.Spherical
open Langlands.GeneralLinear.Iwasawa

universe uK uσ uF uΓ

section Laurent

variable (σ : Type uσ) (K : Type uK) [Fintype σ] [Field K]

/-- The product of the Laurent coordinates is a unit in the symmetric algebra. -/
def symmetricTorusDeterminantUnit : (symmetricTorusSubalgebra σ K)ˣ where
  val := ⟨torusDeterminantUnit σ K, fun e => by
    exact congrArg Units.val (torusPolynomialPermutation_determinantUnit σ K e)⟩
  inv := ⟨(torusDeterminantUnit σ K ^ (-1 : ℤ) :
      (TorusPolynomialAlgebra σ K)ˣ), fun e => by
    rw [algHom_apply_unit_zpow, torusPolynomialPermutation_determinantUnit]⟩
  val_inv := Subtype.ext (by simp)
  inv_val := Subtype.ext (by simp)

@[simp] theorem symmetricTorusDeterminantUnit_val :
    ((symmetricTorusDeterminantUnit σ K : symmetricTorusSubalgebra σ K) :
      TorusPolynomialAlgebra σ K) = torusDeterminantUnit σ K := rfl

@[simp] theorem symmetricTorusEvaluation_determinantUnit (x : σ → Kˣ) :
    Units.map (symmetricTorusEvaluation σ K x).toMonoidHom
      (symmetricTorusDeterminantUnit σ K) = ∏ i, x i := by
  apply Units.ext
  change torusPolynomialEvaluation σ K x (torusDeterminantUnit σ K) = _
  exact congrArg Units.val (torusPolynomialEvaluation_determinantUnit σ K x)

@[simp] theorem symmetricTorusDeterminantUnit_zpow_val (t : ℤ) :
    (((symmetricTorusDeterminantUnit σ K ^ t :
      (symmetricTorusSubalgebra σ K)ˣ) : symmetricTorusSubalgebra σ K) :
      TorusPolynomialAlgebra σ K) =
        (torusDeterminantUnit σ K ^ t : (TorusPolynomialAlgebra σ K)ˣ) := by
  change (symmetricTorusSubalgebra σ K).val
    (symmetricTorusDeterminantUnit σ K ^ t : (symmetricTorusSubalgebra σ K)ˣ) = _
  rw [algHom_apply_unit_zpow]
  have hm : Units.map (symmetricTorusSubalgebra σ K).val.toMonoidHom
      (symmetricTorusDeterminantUnit σ K) = torusDeterminantUnit σ K :=
    Units.ext rfl
  rw [hm]

theorem torusSchur_add_const {n : ℕ} (lam : Fin (n + 1) → ℤ) (t : ℤ) :
    torusSchur K (fun i => lam i + t) =
      (torusDeterminantUnit (Fin (n + 1)) K ^ t :
        (TorusPolynomialAlgebra (Fin (n + 1)) K)ˣ) * torusSchur K lam := by
  have hshift : (fun i => (lam i + t) - (lam (Fin.last n) + t)) =
      (fun i => lam i - lam (Fin.last n)) := by
    funext i
    ring
  simp only [torusSchur, hshift, zpow_add, Units.val_mul]
  ring

theorem symmetricTorusSchur_add_const {n : ℕ} (lam : Fin (n + 1) → ℤ) (t : ℤ) :
    symmetricTorusSchur K (fun i => lam i + t) =
      (symmetricTorusDeterminantUnit (Fin (n + 1)) K ^ t :
        (symmetricTorusSubalgebra (Fin (n + 1)) K)ˣ) *
          symmetricTorusSchur K lam := by
  apply Subtype.ext
  change torusSchur K (fun i => lam i + t) = _
  rw [torusSchur_add_const, Subalgebra.coe_mul,
    symmetricTorusDeterminantUnit_zpow_val]
  rfl

end Laurent

/-- The sum of the Borel modulus weights is zero. -/
theorem sum_borelWeights (n : ℕ) :
    (∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ))) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
      have he (i : Fin (n + 1)) :
          (n : ℤ) + 1 - 2 * (i : ℤ) = ((n : ℤ) - 2 * (i : ℤ)) + 1 := by ring
      simp_rw [he]
      rw [Finset.sum_add_distrib, ih]
      simp
      ring

theorem halfModulus_add_const {n : ℕ} (q : ℕ) (lam : Fin (n + 1) → ℤ) (t : ℤ) :
    halfModulus q (fun i => lam i + t) = halfModulus q lam := by
  have he :
      (∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * (lam i + t)) =
        ∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * lam i := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_borelWeights]
    simp
  simp only [halfModulus, he]

section Central

variable {F : Type uF} [Field F] {Γ₀ : Type uΓ} [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation F Γ₀} {n : ℕ} {ϖ : Fˣ}
variable (hϖ : IsUniformizingElement v ϖ)

theorem torus_add_const (lam : Fin (n + 1) → ℤ) (t : ℤ) :
    torus ϖ (fun i => lam i + t) =
      torus ϖ lam * torus ϖ (fun _ : Fin (n + 1) => t) := by
  rw [torus, torus, torus, ← map_mul]
  congr 1
  funext i
  exact zpow_add _ _ _

theorem torus_const_eq_scalar (t : ℤ) :
    torus ϖ (fun _ : Fin (n + 1) => t) =
      Matrix.GeneralLinearGroup.scalar (Fin (n + 1)) (ϖ ^ t) := rfl

theorem torus_const_commute (t : ℤ)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    torus ϖ (fun _ : Fin (n + 1) => t) * g =
      g * torus ϖ (fun _ : Fin (n + 1) => t) := by
  rw [torus_const_eq_scalar, Matrix.GeneralLinearGroup.scalar_commute]

theorem exponent_mul_torus_const
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) (t : ℤ) :
    exponent hϖ (g * torus ϖ (fun _ : Fin (n + 1) => t)) =
      fun i => exponent hϖ g i + t := by
  obtain ⟨u, hu, k, hk, hg⟩ := exists_eq_exponent hϖ g
  apply exponent_eq hϖ hu hk
  rw [torus_add_const, mul_assoc u, mul_assoc (torus ϖ _),
    torus_const_commute, ← mul_assoc, ← mul_assoc, ← hg]

theorem antitone_add_const_iff (lam : Fin (n + 1) → ℤ) (t : ℤ) :
    Antitone (fun i => lam i + t) ↔ Antitone lam := by
  simp only [Antitone, add_le_add_iff_right]

/-- Central torus translation multiplies the actual spherical polynomial by
the corresponding power of the coordinate product. -/
theorem sphericalWhittakerPolynomial_mul_torus_const
    (θ : upperUnipotent (n + 1) F →* ℂˣ) (q : ℕ)
    (hθ : IsIntegrallyTrivial v θ)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) (t : ℤ) :
    sphericalWhittakerPolynomial hϖ θ q
      (g * torus ϖ (fun _ : Fin (n + 1) => t)) =
      (symmetricTorusDeterminantUnit (Fin (n + 1)) ℂ ^ t :
        (symmetricTorusSubalgebra (Fin (n + 1)) ℂ)ˣ) *
          sphericalWhittakerPolynomial hϖ θ q g := by
  obtain ⟨k, hk, hg⟩ := exists_eq_unipotentPart hϖ g
  by_cases hlam : Antitone (exponent hϖ g)
  · have hs : Antitone (fun i => exponent hϖ g i + t) :=
      (antitone_add_const_iff _ t).2 hlam
    have hshift : g * torus ϖ (fun _ : Fin (n + 1) => t) =
        (unipotentPart hϖ g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) *
          torus ϖ (fun i => exponent hϖ g i + t) * k := by
      rw [torus_add_const, mul_assoc (unipotentPart hϖ g).val,
        mul_assoc (torus ϖ _), torus_const_commute,
        ← mul_assoc, ← mul_assoc, ← hg]
    rw [hshift, sphericalWhittakerPolynomial_of_antitone hϖ θ q hθ _ hs hk,
      halfModulus_add_const, symmetricTorusSchur_add_const]
    conv_rhs =>
      rw [hg, sphericalWhittakerPolynomial_of_antitone hϖ θ q hθ _ hlam hk]
    ring
  · rw [sphericalWhittakerPolynomial_of_not_antitone hϖ θ q g hlam,
      mul_zero, sphericalWhittakerPolynomial_of_not_antitone hϖ θ q _
        (by rwa [exponent_mul_torus_const, antitone_add_const_iff])]

end Central

end Langlands.Conductor
