import Langlands.Representation.Archimedean.ComplexMaximalParabolicIntegration
import Mathlib.MeasureTheory.Group.Integral

/-! # Complex Godement sections in the upper-Borel convention -/

noncomputable section

open MeasureTheory Measure
open scoped ContDiff Manifold Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.GeneralLinear Langlands.Archimedean Langlands.LocalFactor.Archimedean
open ComplexMaximalParabolicIntegration (normSqC normSqC_mul normSqC_ne_zero
  det_upperUnipotent)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩

/-- The normalized absolute value of a complex unit to a complex power. -/
def normPower (s : ℂ) : ℂˣ →* ℂ where
  toFun z := normSqC (z : ℂ) ^ s
  map_one' := by simp [normSqC]
  map_mul' z w := by
    change normSqC ((z : ℂ) * (w : ℂ)) ^ s = _
    rw [normSqC_mul]
    exact Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity) s

/-- The character `d` multiplied by `|·|_ℂ ^ s`. -/
def characterWeight (d : ComplexCharacterData) (s : ℂ) : ℂˣ →* ℂ where
  toFun z := (d.character z : ℂ) * normPower s z
  map_one' := by simp
  map_mul' z w := by simp only [map_mul, Units.val_mul]; ring

private theorem characterWeight_ne_zero (d : ComplexCharacterData) (s : ℂ) (z : ℂˣ) :
    characterWeight d s z ≠ 0 := by
  exact mul_ne_zero (d.character z).ne_zero
    (Complex.cpow_ne_zero_iff.mpr (Or.inl (normSqC_ne_zero z.ne_zero)))

/-- The last `m` rows of a matrix of size `m + 1`. -/
def trailingRows {m : ℕ} (g : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :
    Matrix (Fin m) (Fin (m + 1)) ℂ :=
  g.submatrix Fin.succ id

/-- The integrand in the smaller general linear group in formula (7.1). -/
def godementSectionIntegrand {m : ℕ} (d : ComplexCharacterData)
    (Φ : Matrix (Fin m) (Fin (m + 1)) ℂ → ℂ) (f : Langlands.GeneralLinear m ℂ → ℂ)
    (g : Langlands.GeneralLinear (m + 1) ℂ) (h : Langlands.GeneralLinear m ℂ) : ℂ :=
  Φ (h.val * trailingRows g.val) * f h⁻¹ *
    characterWeight d (((m : ℂ) + 1) / 2) (determinant h)

/-- Formula (7.1) in the upper-Borel model, adjoining `d` before the retained list.
The half-powers of the squared complex norm are the exponents of the modulus in (7.1). -/
def godementSection {m : ℕ} (ν : Measure (Langlands.GeneralLinear m ℂ))
    (d : ComplexCharacterData) (Φ : Matrix (Fin m) (Fin (m + 1)) ℂ → ℂ)
    (f : Langlands.GeneralLinear m ℂ → ℂ) (g : Langlands.GeneralLinear (m + 1) ℂ) : ℂ :=
  characterWeight d ((m : ℂ) / 2) (determinant g) *
    ∫ h, godementSectionIntegrand d Φ f g h ∂ν

private theorem trailingRows_mul {m : ℕ} {p : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ}
    (hp : ∀ i : Fin m, p i.succ 0 = 0) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :
    trailingRows (p * g) = p.submatrix Fin.succ Fin.succ * trailingRows g := by
  ext i j
  simp [trailingRows, Matrix.mul_apply, Fin.sum_univ_succ, hp]

private def trailingUnipotent {m : ℕ} (u : upperUnipotent (m + 1) ℂ) : upperUnipotent m ℂ := by
  let M := u.val.val.submatrix Fin.succ Fin.succ
  have htri : M.IsUpperTriangular := fun i j h => u.2.1 (Fin.succ_lt_succ_iff.mpr h)
  have hdiag (i : Fin m) : M i i = 1 := u.2.2 i.succ
  have hdet : M.det = 1 := by rw [Matrix.det_of_isUpperTriangular htri]; simp [hdiag]
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (hdet ▸ one_ne_zero), htri, hdiag⟩

private theorem trailingRows_borel_mul {m : ℕ} (a : Fin (m + 1) → ℂˣ)
    (u : upperUnipotent (m + 1) ℂ) (g : Langlands.GeneralLinear (m + 1) ℂ) :
    trailingRows ((Iwasawa.diagonalUnits a * u.val * g).val) =
      (Iwasawa.diagonalUnits (fun i : Fin m => a i.succ) * (trailingUnipotent u).val).val *
        trailingRows g.val := by
  change trailingRows (((Iwasawa.diagonalUnits a).val * u.val.val) * g.val) = _
  have hz (i : Fin m) : ((Iwasawa.diagonalUnits a).val * u.val.val) i.succ 0 = 0 := by
    have hu : u.val.val i.succ (0 : Fin (m + 1)) = 0 := u.2.1 (Fin.succ_pos i)
    rw [Iwasawa.diagonalUnits_val, Matrix.diagonal_mul, hu, mul_zero]
  rw [trailingRows_mul hz]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, Units.val_mul, Iwasawa.diagonalUnits_val,
    Matrix.diagonal_mul]
  rfl

private theorem determinant_borel {n : ℕ} (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ) :
    determinant (Iwasawa.diagonalUnits a * u.val) = ∏ i, a i := by
  apply Units.ext
  change ((Iwasawa.diagonalUnits a).val * u.val.val).det = (Units.coeHom ℂ) (∏ i, a i)
  rw [Matrix.det_mul, det_upperUnipotent u, mul_one, Iwasawa.diagonalUnits_val,
    Matrix.det_diagonal, map_prod]
  rfl

private theorem principalSeriesCharacter_cons {m : ℕ} (d : ComplexCharacterData)
    (ds : List ComplexCharacterData) (a : Fin (m + 1) → ℂˣ) :
    principalSeriesCharacter ℂ (m + 1) (complexPositionCharacter (d :: ds)) a *
        normPower (1 / 2) (∏ i : Fin m, a i.succ) =
      characterWeight d ((m : ℂ) / 2) (a 0) *
        principalSeriesCharacter ℂ m (complexPositionCharacter ds) (fun i => a i.succ) := by
  rw [principalSeriesCharacter, Fin.prod_univ_succ, map_prod, mul_assoc,
    ← Finset.prod_mul_distrib, principalSeriesCharacter]
  congr 1
  · have h : (((m + 1 : ℕ) : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ) = (m : ℂ) / 2 := by
      push_cast
      ring
    simp only [Fin.val_zero, h, complexPositionCharacter, Complex.finrank_real_complex]
    rfl
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hi : (((m + 1 : ℕ) : ℂ) - 1) / 2 - ((i.succ : ℕ) : ℂ) + 1 / 2 =
        (((m : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) := by
      push_cast [Fin.val_succ]
      ring
    simp only [Complex.finrank_real_complex, normPower, MonoidHom.coe_mk, OneHom.coe_mk]
    change (complexPositionCharacter ds i (a i.succ) * normSqC (a i.succ : ℂ) ^
        ((((m + 1 : ℕ) : ℂ) - 1) / 2 - ((i.succ : ℕ) : ℂ))) *
        normSqC (a i.succ : ℂ) ^ (1 / 2 : ℂ) =
      complexPositionCharacter ds i (a i.succ) * normSqC (a i.succ : ℂ) ^
        (((m : ℂ) - 1) / 2 - ((i : ℕ) : ℂ))
    rw [mul_assoc, ← Complex.cpow_add _ _ (normSqC_ne_zero (a i.succ).ne_zero), hi]

private theorem characterWeight_add_half (d : ComplexCharacterData) (m : ℕ) (z : ℂˣ) :
    characterWeight d (((m : ℂ) + 1) / 2) z =
      characterWeight d ((m : ℂ) / 2) z * normPower (1 / 2) z := by
  simp only [characterWeight, normPower, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [mul_assoc, ← Complex.cpow_add _ _ (normSqC_ne_zero z.ne_zero)]
  ring_nf

/-- Godement's integral transforms under the upper Borel by the normalized principal-series
character of `d :: ds`. The pointwise covariance uses invariance of the integration measure. -/
theorem godementSection_covariant {m : ℕ} (ν : Measure (Langlands.GeneralLinear m ℂ))
    [IsMulRightInvariant ν] (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    (Φ : Matrix (Fin m) (Fin (m + 1)) ℂ → ℂ) {f : Langlands.GeneralLinear m ℂ → ℂ}
    (hf : f ∈ complexStandardModule m ds) (a : Fin (m + 1) → ℂˣ)
    (u : upperUnipotent (m + 1) ℂ) (g : Langlands.GeneralLinear (m + 1) ℂ) :
    godementSection ν d Φ f (Iwasawa.diagonalUnits a * u.val * g) =
      principalSeriesCharacter ℂ (m + 1) (complexPositionCharacter (d :: ds)) a *
        godementSection ν d Φ f g := by
  let p : Langlands.GeneralLinear (m + 1) ℂ := Iwasawa.diagonalUnits a * u.val
  let b : Langlands.GeneralLinear m ℂ :=
    Iwasawa.diagonalUnits (fun i : Fin m => a i.succ) * (trailingUnipotent u).val
  let w := characterWeight d ((m : ℂ) / 2)
  let v := characterWeight d (((m : ℂ) + 1) / 2)
  let c := principalSeriesCharacter ℂ m (complexPositionCharacter ds) (fun i => a i.succ)
  let C := principalSeriesCharacter ℂ (m + 1) (complexPositionCharacter (d :: ds)) a
  have hb : determinant b = ∏ i : Fin m, a i.succ := determinant_borel _ _
  have hp : determinant p = a 0 * determinant b := by
    dsimp only [p]
    rw [determinant_borel, Fin.prod_univ_succ, hb]
  have hfactor : w (determinant p) * c = C * v (determinant b) := by
    have hc : C * normPower (1 / 2) (determinant b) = w (a 0) * c := by
      rw [hb]
      exact principalSeriesCharacter_cons d ds a
    calc
      w (determinant p) * c = (w (a 0) * c) * w (determinant b) := by
        rw [hp, map_mul]
        ring
      _ = C * v (determinant b) := by
        dsimp only [v]
        rw [characterWeight_add_half, ← hc]
        ring
  let kernel := godementSectionIntegrand d Φ f
  have hK (h : Langlands.GeneralLinear m ℂ) :
      v (determinant b) * kernel (p * g) h = c * kernel g (h * b) := by
    have hF : f h⁻¹ = c * f ((h * b)⁻¹) := by
      have h' := hf.2 (fun i : Fin m => a i.succ) (trailingUnipotent u) ((h * b)⁻¹)
      change f (b * (h * b)⁻¹) = c * f ((h * b)⁻¹) at h'
      simpa only [mul_inv_rev, mul_inv_cancel_left] using h'
    have hr : trailingRows (p * g).val = b.val * trailingRows g.val :=
      trailingRows_borel_mul a u g
    have hval : h.val * b.val = (h * b).val := rfl
    have hdet : v (determinant (h * b)) = v (determinant h) * v (determinant b) := by
      rw [map_mul determinant h b, map_mul v]
    dsimp only [kernel, godementSectionIntegrand]
    rw [hr, ← Matrix.mul_assoc, hval, hF, hdet]
    ring
  have hI : v (determinant b) * (∫ h, kernel (p * g) h ∂ν) =
      c * (∫ h, kernel g h ∂ν) := by
    calc
      _ = ∫ h, v (determinant b) * kernel (p * g) h ∂ν := (integral_const_mul _ _).symm
      _ = ∫ h, c * kernel g (h * b) ∂ν := integral_congr_ae (Filter.Eventually.of_forall hK)
      _ = _ := by rw [integral_const_mul, integral_mul_right_eq_self]
  change w (determinant (p * g)) * (∫ h, kernel (p * g) h ∂ν) =
    C * (w (determinant g) * ∫ h, kernel g h ∂ν)
  rw [map_mul determinant, map_mul w]
  apply mul_left_cancel₀ (characterWeight_ne_zero d _ (determinant b))
  calc
    _ = w (determinant p) * w (determinant g) *
        (v (determinant b) * ∫ h, kernel (p * g) h ∂ν) := by ring
    _ = _ := by rw [hI, ← mul_assoc, mul_right_comm (w (determinant p)), hfactor]; ring

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
