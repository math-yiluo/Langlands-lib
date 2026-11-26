import Langlands.Global.RankinSelberg.ComplexHolomorphicGaussianMean
import Langlands.Global.RankinSelberg.ComplexGodementStandardGaussians
import Langlands.Representation.GodementJacquet.ComplexTriangularZetaIntegral
import Langlands.Global.RankinSelberg.ComplexCompactProfileFamily

/-! # Angular tests for the complex square matrix integral -/

noncomputable section

open MeasureTheory MvPolynomial Set
open scoped ComplexConjugate Matrix.Norms.Operator NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexGramFormula (phaseUnit norm_phaseUnit)
open Langlands.Archimedean.ComplexPrincipalSeriesExtension (phaseMatrix phaseMatrix_val)
open Langlands.GeneralLinear (UpperEntryPair upperEntryProductMeasure)
open Langlands.GodementJacquet (complexTriangularMatrix)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.LocalFactor.ComplexTate (gaussian)
open ComplexCompactProfileFamily (IsCompactProfile)
open ComplexGodementGaussianPolynomial (Coordinates coordinates coordinates_re coordinates_im matrixSqNorm
  matrixGaussian matrixGaussian_mul_unitary gaussianPolynomial gaussianPolynomial_apply
  finiteDimensional_rightTranslate_gaussianPolynomial)
open HolomorphicGaussianMean (holomorphicGaussianMean)

variable {n : ℕ}

local notation "I" => Fin n
local notation "W" => I → ℕ
local notation "Mat" => Matrix I I ℂ
local notation "K" => unitaryCompact ℂ n
local notation "U" => Matrix.unitaryGroup I ℂ
local notation "Off" => UpperEntryPair n
local notation "Idx" => Coordinates n n
local notation "Poly" => MvPolynomial Idx ℂ
local notation "scale" => (2 * Real.pi : ℝ)

private abbrev Layer (w : W) (t : ℕ) := {i : I // t < w i}

private def layerMinor (w : W) (t : ℕ) (A : Mat) : ℂ :=
  (A.submatrix (Subtype.val : Layer w t → I) Subtype.val).det

private def layerProduct (w : W) (A : Mat) : ℂ :=
  ∏ t ∈ Finset.range (Finset.univ.sup w), layerMinor w t A

private theorem layerProduct_one (w : W) : layerProduct w 1 = 1 := by
  unfold layerProduct layerMinor
  simp only [Matrix.submatrix_one _ Subtype.val_injective, Matrix.det_one, Finset.prod_const_one]

private theorem layerMinor_mul (w : W) (t : ℕ) (A B : Mat) (hA : A.IsUpperTriangular)
    (hZ : ∀ i j, w j < w i → A i j = 0) :
    layerMinor w t (A * B) = (∏ j : Layer w t, A j.val j.val) * layerMinor w t B := by
  let e : Layer w t → I := Subtype.val
  have hEq : (A * B).submatrix e e = A.submatrix e e * B.submatrix e e := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply]
    refine (Fintype.sum_of_injective e Subtype.val_injective _ _ (fun x hx => ?_) (fun _ => rfl)).symm
    have hX : ¬ t < w x := fun h => hx ⟨⟨x, h⟩, rfl⟩
    rw [hZ i.val x ((le_of_not_gt hX).trans_lt i.2), zero_mul]
  unfold layerMinor
  change ((A * B).submatrix e e).det = _ * (B.submatrix e e).det
  rw [hEq, Matrix.det_mul]
  congr 1
  exact Matrix.det_of_isUpperTriangular (fun i j hij => hA hij)

private theorem layerProduct_mul (w : W) (A B : Mat) (hA : A.IsUpperTriangular)
    (hZ : ∀ i j, w j < w i → A i j = 0) :
    layerProduct w (A * B) = (∏ i, A i i ^ w i) * layerProduct w B := by
  simp only [layerProduct, layerMinor_mul w _ A B hA hZ, Finset.prod_mul_distrib]
  congr 1
  have he (t : ℕ) : (∏ j : Layer w t, A j.val j.val) =
      ∏ j ∈ Finset.univ.filter (fun i => t < w i), A j j :=
    (Finset.prod_subtype _ (fun j => by simp) (fun j => A j j)).symm
  simp_rw [he]
  rw [Finset.prod_comm' (t' := Finset.univ) (s' := fun i : I => Finset.range (w i))]
  · simp only [Finset.prod_const, Finset.card_range]
  · intro t i
    simp only [Finset.mem_range, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
    exact ⟨fun h => h.2, fun h => ⟨h.trans_le (Finset.le_sup (Finset.mem_univ i)), h⟩⟩

private theorem layerProduct_diagonal (w : W) (d : I → ℂ) (B : Mat) :
    layerProduct w (Matrix.diagonal d * B) = (∏ i, d i ^ w i) * layerProduct w B := by
  rw [layerProduct_mul w _ B]
  · simp
  · intro i j hij
    exact Matrix.diagonal_apply_ne _ (ne_of_gt hij)
  · intro i j hij
    exact Matrix.diagonal_apply_ne _ (ne_of_apply_ne w (ne_of_gt hij))

private def layerPolynomial {ι : Type*} (w : W) (A : Matrix I I (MvPolynomial ι ℂ)) : MvPolynomial ι ℂ :=
  ∏ t ∈ Finset.range (Finset.univ.sup w),
    (A.submatrix (Subtype.val : Layer w t → I) Subtype.val).det

private theorem eval_layerPolynomial {ι : Type*} (x : ι → ℂ) (w : W)
    (A : Matrix I I (MvPolynomial ι ℂ)) :
    eval x (layerPolynomial w A) = layerProduct w (A.map (eval x)) := by
  simp only [layerPolynomial, layerProduct, layerMinor, map_prod, RingHom.map_det]
  rfl

private def entryPolynomial (b : Bool) (i j : I) : Poly :=
  X (i, j, false) + C (if b then -Complex.I else Complex.I) * X (i, j, true)

private theorem eval_entryPolynomial (b : Bool) (A : Mat) (i j : I) :
    eval (coordinates A) (entryPolynomial b i j) = if b then conj (A i j) else A i j := by
  cases b <;> simp only [entryPolynomial, coordinates_re, coordinates_im, map_add, map_mul, eval_X,
    eval_C, Bool.false_eq_true, ite_false, ite_true]
  · rw [mul_comm Complex.I]
    exact Complex.re_add_im (A i j)
  · apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]

private def negativePart (w : I → ℤ) : W := fun i => (-w i).toNat
private def positivePart (w : I → ℤ) : W := fun i => (w i).toNat

private def angularMultiplier (w : I → ℤ) (A : Mat) : ℂ :=
  layerProduct (negativePart w) A * conj (layerProduct (positivePart w) A)

private def angularPolynomial (w : I → ℤ) (b : Bool) : Poly :=
  layerPolynomial (negativePart w) (Matrix.of (entryPolynomial b)) *
    layerPolynomial (positivePart w) (Matrix.of (entryPolynomial (!b)))

private theorem layerProduct_conj (w : W) (A : Mat) :
    layerProduct w (A.map (starRingEnd ℂ)) = conj (layerProduct w A) := by
  simp only [layerProduct, layerMinor, map_prod, RingHom.map_det]
  rfl

private theorem eval_angularPolynomial (w : I → ℤ) (b : Bool) (A : Mat) :
    eval (coordinates A) (angularPolynomial w b) = if b then conj (angularMultiplier w A) else angularMultiplier w A := by
  have h (c : Bool) : (Matrix.of (entryPolynomial c)).map (eval (coordinates A)) =
      if c then A.map (starRingEnd ℂ) else A := by
    ext i j
    cases c
    · simpa only [Matrix.map_apply, Matrix.of_apply, Bool.false_eq_true, ite_false] using
        eval_entryPolynomial false A i j
    · simpa only [Matrix.map_apply, Matrix.of_apply, ite_true] using eval_entryPolynomial true A i j
  simp only [angularPolynomial, map_mul, eval_layerPolynomial, h]
  cases b <;> simp [angularMultiplier, layerProduct_conj]

private def angularProfile (w : I → ℤ) (k : U) : ℂ := conj (angularMultiplier w k.val)

private theorem angularProfile_one (w : I → ℤ) : angularProfile w 1 = 1 := by
  simp [angularProfile, angularMultiplier, layerProduct_one]

private theorem angularProfile_continuous (w : I → ℤ) : Continuous (angularProfile w) := by
  have h (v : W) : Continuous (fun k : U => layerProduct v k.val) := by
    apply continuous_finsetProd
    intro t _
    unfold layerMinor
    apply Continuous.matrix_det
    apply continuous_matrix
    intro i j
    exact (continuous_apply j.val).comp ((continuous_apply i.val).comp continuous_subtype_val)
  exact Complex.continuous_conj.comp ((h _).mul (Complex.continuous_conj.comp (h _)))

private theorem angularProfile_finite (w : I → ℤ) :
    FiniteDimensional ℂ (Submodule.span ℂ (range fun k : U => fun x => angularProfile w (x * k))) := by
  let p := angularPolynomial w true
  let E := Submodule.span ℂ (range fun k : K => fun A : Mat => gaussianPolynomial p (A * k.val.val))
  let : FiniteDimensional ℂ E := finiteDimensional_rightTranslate_gaussianPolynomial p
  let c := matrixGaussian (1 : Mat)
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  let T : (Mat → ℂ) →ₗ[ℂ] (U → ℂ) :=
    { toFun F x := c⁻¹ * F x.val
      map_add' F G := by
        funext x
        exact mul_add _ _ _
      map_smul' b F := by
        funext x
        exact mul_left_comm c⁻¹ b (F x.val) }
  apply Submodule.finiteDimensional_of_le (S₂ := E.map T)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  let k' : K := ⟨Unitary.toUnits k, k.2⟩
  refine ⟨_, Submodule.subset_span ⟨k', rfl⟩, ?_⟩
  funext x
  have hx : matrixGaussian (x.val * k.val) = c := by
    let v : K := ⟨Unitary.toUnits (x * k), (x * k).2⟩
    show matrixGaussian v.val.val = matrixGaussian (1 : Mat)
    simpa only [one_mul] using matrixGaussian_mul_unitary (1 : Mat) v
  change c⁻¹ * gaussianPolynomial p (x.val * k.val) = _
  rw [gaussianPolynomial_apply, eval_angularPolynomial, ite_eq_left rfl, hx,
    mul_left_comm, inv_mul_cancel₀ hc, mul_one]
  rfl

private theorem phase_conj_eq_inv (a : ℂˣ) : conj ((phaseUnit a : ℂˣ) : ℂ) = ((phaseUnit a : ℂˣ) : ℂ)⁻¹ := by
  rw [← one_div]
  apply (eq_div_iff (phaseUnit a).ne_zero).mpr
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_phaseUnit]
  norm_num

private theorem angularProfile_covariant (w : I → ℤ) (a : I → ℂˣ) (k : U) :
    angularProfile w (phaseMatrix a * k) =
      (∏ i, ((phaseUnit (a i) : ℂˣ) : ℂ) ^ w i) * angularProfile w k := by
  let d (i : I) : ℂ := (phaseUnit (a i) : ℂˣ)
  change conj (angularMultiplier w ((phaseMatrix a).val * k.val)) = _
  simp only [phaseMatrix_val, angularMultiplier, angularProfile, layerProduct_diagonal, map_mul,
    map_prod, map_pow, Complex.conj_conj]
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  change conj (d i) ^ (-w i).toNat * d i ^ (w i).toNat = d i ^ w i
  rw [phase_conj_eq_inv]
  rcases le_or_gt 0 (w i) with hi | hi
  · rw [Int.toNat_of_nonpos (neg_nonpos.mpr hi), pow_zero, one_mul, ← zpow_natCast, Int.toNat_of_nonneg hi]
  · rw [Int.toNat_of_nonpos hi.le, pow_zero, mul_one, inv_pow, ← zpow_natCast, ← zpow_neg,
      Int.toNat_of_nonneg (neg_nonneg.mpr hi.le), neg_neg]

private theorem angularProfile_isCompactProfile (w : I → ℤ) : IsCompactProfile w (angularProfile w) :=
  ⟨angularProfile_continuous w, angularProfile_finite w, angularProfile_covariant w⟩

private def triangularPolynomial (d : I → ℂ) : Matrix I I (MvPolynomial Off ℂ) :=
  Matrix.of fun i j => if h : i < j then X ⟨(i, j), h⟩ else if i = j then C (d i) else 0

private theorem eval_triangularPolynomial (z : Off → ℂ) (d : I → ℂ) :
    (triangularPolynomial d).map (eval z) = complexTriangularMatrix d z := by
  ext i j
  simp only [triangularPolynomial, complexTriangularMatrix, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

private theorem upper_complexTriangularMatrix (d : I → ℂ) (u : Off → ℂ) :
    (complexTriangularMatrix d u).IsUpperTriangular := by
  intro i j h
  change j < i at h
  simp [complexTriangularMatrix, not_lt_of_gt h, ne_of_gt h]

private theorem layerProduct_triangular (w : W) (hw : Monotone w) (d : I → ℂ) (u : Off → ℂ) (B : Mat) :
    layerProduct w (complexTriangularMatrix d u * B) = (∏ i, d i ^ w i) * layerProduct w B := by
  rw [layerProduct_mul _ _ _ (upper_complexTriangularMatrix d u)]
  · simp [complexTriangularMatrix]
  · intro i j h
    exact upper_complexTriangularMatrix d u (lt_of_not_ge fun hl => h.not_ge (hw hl))

private theorem triangular_zero (d : I → ℂ) :
    complexTriangularMatrix d (fun _ => 0) = Matrix.diagonal d := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [complexTriangularMatrix]
  · simp [complexTriangularMatrix, h]

private theorem angularTate_eq (m : ℤ) (z : ℂ) :
    z ^ (-m).toNat * conj z ^ m.toNat * (Real.exp (-scale * ‖z‖ ^ 2) : ℂ) =
      (Real.pi : ℂ) * gaussian m z := by
  have hE : (Real.exp (-scale * ‖z‖ ^ 2) : ℂ) =
      Complex.exp (-2 * (Real.pi : ℂ) * (‖z‖ : ℂ) ^ 2) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hE, gaussian, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
  rcases le_or_gt 0 m with hm | hm
  · have h : m.toNat = m.natAbs := by omega
    simp only [ite_eq_left hm, Int.toNat_of_nonpos (neg_nonpos.mpr hm), pow_zero, one_mul, h]
  · have h : (-m).toNat = m.natAbs := by omega
    simp only [ite_eq_right hm.not_ge, Int.toNat_of_nonpos hm.le, pow_zero, mul_one, h]

private theorem squareGaussian_triangular_unitary (d : I → ℂ) (u : Off → ℂ) (k : K) :
    (Real.exp (-scale * matrixSqNorm (complexTriangularMatrix d u * k.val.val)) : ℂ) =
      (∏ i, (Real.exp (-scale * ‖d i‖ ^ 2) : ℂ)) * (Real.exp (-scale * ∑ j, ‖u j‖ ^ 2) : ℂ) := by
  have hT : complexTriangularMatrix d u = ComplexGodement.upperTriangularEntries d u := rfl
  rw [hT, matrixSqNorm_mul_unitary, matrixSqNorm_upperTriangularEntries, mul_add, Real.exp_add,
    Finset.mul_sum, Real.exp_sum, Complex.ofReal_mul, Complex.ofReal_prod]

private theorem angularGaussian_triangular_mean (w : I → ℤ) (hw : Monotone w)
    (ν : AdditiveHaarMeasure ℂ) (d : I → ℂ) (k : K) :
    let γ (u : Off → ℂ) := (Real.exp (-scale * ∑ j, ‖u j‖ ^ 2) : ℂ)
    let c := ∫ u, γ u ∂upperEntryProductMeasure ν n
    c ≠ 0 ∧
      (∫ u, squarePolynomialGaussian (angularPolynomial w false)
        (complexTriangularMatrix d u * k.val.val) ∂upperEntryProductMeasure ν n) =
        c * conj (angularProfile w ⟨k.val.val, k.2⟩) * ∏ i, (Real.pi : ℂ) * gaussian (w i) (d i) := by
  intro γ c
  let : ν.measure.IsAddHaarMeasure := ν.isAddHaar
  have ⟨hc, hMean⟩ := holomorphicGaussianMean (ι := Off) ν.measure
  let A := k.val.val
  let p := layerPolynomial (negativePart w) (triangularPolynomial d * A.map C)
  have hp (u : Off → ℂ) :
      eval u p = layerProduct (negativePart w) (complexTriangularMatrix d u * A) := by
    change eval u (layerPolynomial (negativePart w) (triangularPolynomial d * A.map C)) = _
    rw [eval_layerPolynomial, Matrix.map_mul, eval_triangularPolynomial]
    congr 2
    ext i j
    exact eval_C _
  have hPos : Monotone (positivePart w) := fun i j h => Int.toNat_le_toNat (hw h)
  let g : ℂ := (∏ i, (Real.exp (-scale * ‖d i‖ ^ 2) : ℂ)) *
    conj ((∏ i, d i ^ positivePart w i) * layerProduct (positivePart w) A)
  have hF (u : Off → ℂ) : squarePolynomialGaussian (angularPolynomial w false)
      (complexTriangularMatrix d u * A) = g * (eval u p * γ u) := by
    change eval (coordinates (complexTriangularMatrix d u * A)) (angularPolynomial w false) *
      (Real.exp (-scale * matrixSqNorm (complexTriangularMatrix d u * A)) : ℂ) = _
    rw [eval_angularPolynomial, ite_eq_right Bool.false_ne_true, angularMultiplier,
      layerProduct_triangular _ hPos, squareGaussian_triangular_unitary, hp]
    dsimp only [g, γ]
    ring
  refine ⟨hc, ?_⟩
  have hI : (∫ u, squarePolynomialGaussian (angularPolynomial w false)
      (complexTriangularMatrix d u * A) ∂upperEntryProductMeasure ν n) =
      g * ∫ u, eval u p * γ u ∂upperEntryProductMeasure ν n := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ hF)
  rw [hI]
  change g * (∫ u, eval u p * γ u ∂Measure.pi (fun _ : Off => ν.measure)) = _
  rw [(hMean p).2, hp, triangular_zero, layerProduct_diagonal]
  simp only [g, angularProfile, angularMultiplier, Complex.conj_conj, map_mul, map_prod, map_pow]
  have hT : (∏ i, (Real.pi : ℂ) * gaussian (w i) (d i)) =
      (∏ i, d i ^ negativePart w i) * (∏ i, conj (d i) ^ positivePart w i) *
        ∏ i, (Real.exp (-scale * ‖d i‖ ^ 2) : ℂ) := by
    simp_rw [← angularTate_eq]
    simp only [Finset.prod_mul_distrib, negativePart, positivePart]
  rw [hT]
  dsimp only [A, c, γ, upperEntryProductMeasure]
  ring

/-- For nondecreasing angular weights, a standard square polynomial Gaussian has an upper-entry
mean equal to the exact scalar angular Tate tests times the conjugate of a nonzero compact profile
of the original weights. -/
def ComplexSquareZetaAngularTestStatement : Prop :=
  ∀ w : I → ℤ, Monotone w → ∃ (p : Poly) (f : U → ℂ), IsCompactProfile w f ∧ f 1 = 1 ∧
    ∀ (ν : AdditiveHaarMeasure ℂ),
      ∃ c : ℂ, c ≠ 0 ∧ ∀ (d : I → ℂ) (k : K),
        (∫ u, squarePolynomialGaussian p
          (complexTriangularMatrix d u * k.val.val) ∂upperEntryProductMeasure ν n) =
          c * conj (f ⟨k.val.val, k.2⟩) * ∏ i, (Real.pi : ℂ) * gaussian (w i) (d i)

theorem complexSquareZetaAngularTest : ComplexSquareZetaAngularTestStatement (n := n) := by
  intro w hw
  refine ⟨angularPolynomial w false, angularProfile w, angularProfile_isCompactProfile w,
    angularProfile_one w, fun ν => ?_⟩
  let γ (u : Off → ℂ) := (Real.exp (-scale * ∑ j, ‖u j‖ ^ 2) : ℂ)
  refine ⟨∫ u, γ u ∂upperEntryProductMeasure ν n, ?_, fun d k => ?_⟩
  · exact (angularGaussian_triangular_mean w hw ν 0 1).1
  · exact (angularGaussian_triangular_mean w hw ν d k).2

end Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta
