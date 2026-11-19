import Langlands.Global.RankinSelberg.ComplexGodementSection
import Langlands.Global.RankinSelberg.ComplexGodementTriangularEntries

/-! # Diagonal weights in the complex Godement integral -/

noncomputable section

open scoped Matrix.Norms.Operator NNReal

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.ComplexMaximalParabolicIntegration
  (normSqC normSqC_ne_zero normSqC_det_unitary det_upperUnipotent)
open Langlands.GeneralLinear.Iwasawa (diagonalUnits diagonalUnits_val)

set_option autoImplicit false

/-- The diagonal character quotient weighted by the first Mellin power in each position. -/
def diagonalTateWeight {n : ℕ} (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    (a : Fin n → ℂˣ) : ℂ :=
  ∏ j : Fin n, ((d.character (a j) : ℂ) * complexPositionCharacter ds j (a j)⁻¹) *
    normPower 1 (a j)

private theorem normPower_add (s t : ℂ) (z : ℂˣ) :
    normPower (s + t) z = normPower s z * normPower t z :=
  Complex.cpow_add s t (normSqC_ne_zero z.ne_zero)

private theorem normPower_neg_arg (s : ℂ) (z : ℂˣ) :
    normPower s z⁻¹ = normPower (-s) z := by
  change ((‖((z⁻¹ : ℂˣ) : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ s =
    ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (-s)
  rw [Units.val_inv_eq_inv_val, norm_inv, inv_pow, Complex.ofReal_inv,
    Complex.inv_cpow_ofReal_nonneg (sq_nonneg _), Complex.cpow_neg]

/-- The column density, inverted Borel covariance and added determinant weight combine to the
one-variable Tate weight in each diagonal position. -/
theorem diagonalTateWeight_eq {n : ℕ} (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    (a : Fin n → ℂˣ) :
    (∏ j : Fin n, normPower (-((j : ℕ) : ℂ)) (a j)) *
      (principalSeriesCharacter ℂ n (complexPositionCharacter ds) (fun j => (a j)⁻¹) *
        characterWeight d (((n : ℂ) + 1) / 2) (∏ j, a j)) = diagonalTateWeight d ds a := by
  rw [principalSeriesCharacter, map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Complex.finrank_real_complex]
  let z := a j
  let w : ℂ := ((n : ℂ) - 1) / 2 - ((j : ℕ) : ℂ)
  let b : ℂ := ((n : ℂ) + 1) / 2
  change normPower (-((j : ℕ) : ℂ)) z *
      ((complexPositionCharacter ds j z⁻¹ * normPower w z⁻¹) *
        ((d.character z : ℂ) * normPower b z)) =
    ((d.character z : ℂ) * complexPositionCharacter ds j z⁻¹) * normPower 1 z
  rw [normPower_neg_arg]
  have h : -((j : ℕ) : ℂ) + -w + b = 1 := by dsimp [w, b]; ring
  calc
    _ = ((d.character z : ℂ) * complexPositionCharacter ds j z⁻¹) *
        ((normPower (-((j : ℕ) : ℂ)) z * normPower (-w) z) * normPower b z) := by ring
    _ = _ := by rw [← normPower_add, ← normPower_add, h]

/-- On the positive diagonal, the Jacobian of additive triangular entries is the product of
these inverse normalized powers. -/
theorem upperEntryJacobian_eq_normPower {n : ℕ} (y : Fin n → ℝ) (a : Fin n → ℂˣ)
    (ha : ∀ i, (a i : ℂ) = (Real.exp (y i) : ℂ)) :
    (((upperEntryJacobian y : ℝ≥0) : ℝ) : ℂ) =
      ∏ j : Fin n, normPower (-((j : ℕ) : ℂ)) (a j) := by
  rw [upperEntryJacobian_coe, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  change (((((Real.exp (y j) ^ 2)⁻¹) ^ j.val : ℝ) : ℂ)) = normSqC (a j : ℂ) ^ (-((j : ℕ) : ℂ))
  rw [ha, normSqC, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Complex.cpow_neg, Complex.cpow_natCast, Complex.ofReal_pow, Complex.ofReal_inv, inv_pow]

private theorem determinant_triangular {n : ℕ} (a : Fin n → ℂˣ)
    (u : Langlands.GeneralLinear.upperUnipotent n ℂ) (k : unitaryCompact ℂ n) :
    determinant (k.val * u.val * diagonalUnits a) = determinant k.val * ∏ j, a j := by
  apply Units.ext
  change ((k.val.val * u.val.val) * (diagonalUnits a).val).det =
    (k.val.val.det * Units.coeHom ℂ (∏ j, a j))
  rw [Matrix.det_mul, Matrix.det_mul, det_upperUnipotent u, mul_one,
    diagonalUnits_val, Matrix.det_diagonal, map_prod]
  rfl

/-- After the column Jacobian is included, the Godement integrand in unitary–unipotent–diagonal
order has its inducing weights only in the diagonal Tate factor. -/
theorem godementSectionIntegrand_triangular {n : ℕ} (d : ComplexCharacterData)
    (ds : List ComplexCharacterData) (Φ : Matrix (Fin n) (Fin (n + 1)) ℂ → ℂ)
    {f : Langlands.GeneralLinear n ℂ → ℂ} (hf : f ∈ complexStandardModule n ds)
    (g : Langlands.GeneralLinear (n + 1) ℂ) (u : Langlands.GeneralLinear.upperUnipotent n ℂ)
    (k : unitaryCompact ℂ n) (y : Fin n → ℝ) (a : Fin n → ℂˣ)
    (ha : ∀ i, (a i : ℂ) = (Real.exp (y i) : ℂ)) :
    (((upperEntryJacobian y : ℝ≥0) : ℝ) : ℂ) *
      godementSectionIntegrand d Φ f g (k.val * u.val * diagonalUnits a) =
    Φ (k.val.val * upperTriangularEntries (fun i => (Real.exp (y i) : ℂ))
      (scaleUpperEntries y (Langlands.GeneralLinear.upperEntryCoordinates n u)) *
      trailingRows g.val) *
      (f k.val⁻¹ * (d.character (determinant k.val) : ℂ)) * diagonalTateWeight d ds a := by
  have hcov : f (k.val * u.val * diagonalUnits a)⁻¹ =
      principalSeriesCharacter ℂ n (complexPositionCharacter ds) (fun j => (a j)⁻¹) *
        f k.val⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, ← mul_assoc, ← map_inv]
    exact hf.2 (fun j => (a j)⁻¹) u⁻¹ k.val⁻¹
  have hcompact : characterWeight d (((n : ℂ) + 1) / 2) (determinant k.val) =
      (d.character (determinant k.val) : ℂ) := by
    change (d.character (determinant k.val) : ℂ) *
      normSqC k.val.val.det ^ (((n : ℂ) + 1) / 2) = _
    rw [normSqC_det_unitary, Complex.one_cpow, mul_one]
  rw [godementSectionIntegrand, hcov, determinant_triangular, map_mul, hcompact,
    upperEntryJacobian_eq_normPower y a ha]
  have hmatrix : (k.val * u.val * diagonalUnits a).val =
      k.val.val * upperTriangularEntries (fun i => (Real.exp (y i) : ℂ))
        (scaleUpperEntries y (Langlands.GeneralLinear.upperEntryCoordinates n u)) := by
    rw [mul_assoc, Units.val_mul, unipotent_mul_positiveDiagonal_val u y a ha]
  rw [← hmatrix, ← diagonalTateWeight_eq]
  ring

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
