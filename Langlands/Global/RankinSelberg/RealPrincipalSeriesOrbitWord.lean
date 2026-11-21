import Langlands.Global.RankinSelberg.RealPrincipalSeriesCoefficientGrowth

/-! # Joint continuity and height bounds of translated real derivative words -/

noncomputable section

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open RealPlaceRestriction

open scoped Matrix.Norms.Frobenius in
/-- The height formed from forward and inverse entries is continuous. -/
theorem continuous_realMatrixHeight {m : ℕ} :
    Continuous (realMatrixHeight (n := m)) := by
  change Continuous (fun g : Langlands.GeneralLinear m ℝ => realMatrixHeight g)
  simp_rw [realMatrixHeight_eq_frobenius]
  exact (Units.continuous_val.norm.pow 2).add (Units.continuous_coe_inv.norm.pow 2)

open scoped Matrix.Norms.Frobenius in
/-- The real matrix height is submultiplicative. -/
theorem realMatrixHeight_mul_le {m : ℕ} (x y : Langlands.GeneralLinear m ℝ) :
    realMatrixHeight (x * y) ≤ realMatrixHeight x * realMatrixHeight y := by
  rw [realMatrixHeight_eq_frobenius, realMatrixHeight_eq_frobenius x, realMatrixHeight_eq_frobenius y]
  have h₁ := Matrix.frobenius_norm_mul x.val y.val
  have h₂ := Matrix.frobenius_norm_mul (y⁻¹).val (x⁻¹).val
  simp only [Units.val_mul, mul_inv_rev]
  calc
    _ ≤ (‖x.val‖ * ‖y.val‖)^2 + (‖(y⁻¹).val‖ * ‖(x⁻¹).val‖)^2 := by
      exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) h₁ 2)
        (pow_le_pow_left₀ (norm_nonneg _) h₂ 2)
    _ ≤ _ := by
      nlinarith [mul_nonneg (sq_nonneg ‖x.val‖) (sq_nonneg ‖(y⁻¹).val‖),
        mul_nonneg (sq_nonneg ‖(x⁻¹).val‖) (sq_nonneg ‖y.val‖)]

namespace RealPrincipalSeries

variable (r : ℕ) (ds : List RealBlock)
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "I" => Fin (r + 1)
local notation "Mat" => Matrix I I ℝ
local notation "P" => principalSeries ℝ (r + 1) (realPositionCharacter ds)
local notation "D" => rightDerivative (matrixModel ℝ (r + 1))
local notation "word" => RealLocalWhittaker.iteratedRightDerivative r

/-- Apply a right derivative word to the right-translated section, then evaluate at `x`. -/
def orbitWord (Xs : List Mat) (f : P) (g x : G) : ℂ := word Xs (translate r ds g f) x

theorem orbitWord_nil (f : P) (g x : G) : orbitWord r ds [] f g x = (f : G → ℂ) (x * g) := rfl

theorem orbitWord_cons (Xs : List Mat) (X : Mat) (f : P) (g : G) :
    orbitWord r ds (X :: Xs) f g = D X (orbitWord r ds Xs f g) := rfl

private def orbitDerivative (X : Mat) : P →ₗ[ℂ] P :=
  (rightDerivativeLinearMap P (fun _ h => h.1) X).codRestrict P
    (fun f => rightDerivative_mem_principalSeries _ f.2 X)

private def orbitDerivativeWord (Xs : List Mat) : P →ₗ[ℂ] P :=
  Xs.foldr (fun X B => (orbitDerivative r ds X).comp B) LinearMap.id

private theorem orbitDerivativeWord_apply (Xs : List Mat) (f : P) :
    (orbitDerivativeWord r ds Xs f : G → ℂ) = word Xs f := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
    change D X (orbitDerivativeWord r ds Xs f) = D X (word Xs f)
    rw [ih]

theorem smooth_orbitWord_point (Xs : List Mat) (f : P) (g : G) :
    ContMDiff (matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ (orbitWord r ds Xs f g) := by
  change ContMDiff (matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞ (word Xs (translate r ds g f))
  rw [← orbitDerivativeWord_apply]
  exact (orbitDerivativeWord r ds Xs (translate r ds g f)).2.1

private theorem orbitDerivativeWord_append_singleton (Xs : List Mat) (X : Mat) (f : P) :
    orbitDerivativeWord r ds (Xs ++ [X]) f = orbitDerivativeWord r ds Xs (orbitDerivative r ds X f) := by
  induction Xs with
  | nil => rfl
  | cons Y Xs ih =>
    change orbitDerivative r ds Y (orbitDerivativeWord r ds (Xs ++ [X]) f) =
      orbitDerivative r ds Y (orbitDerivativeWord r ds Xs (orbitDerivative r ds X f))
    rw [ih]

private def adjDir (g : G) (X : Mat) : Mat := (g⁻¹).val * X * g.val

private theorem orbitDerivative_translate (f : P) (g x : G) (X : Mat) :
    (orbitDerivative r ds X (translate r ds g f) : G → ℂ) x =
      (orbitDerivative r ds (adjDir r g X) f : G → ℂ) (x * g) := by
  have h := KIntegralInvariance.rightDerivative_mul_eq f.2.1 g x (adjDir r g X)
  have hX : g.val * adjDir r g X * (g⁻¹).val = X := by
    calc
      _ = (g.val * (g⁻¹).val) * X * (g.val * (g⁻¹).val) := by simp only [adjDir, Matrix.mul_assoc]
      _ = _ := by rw [g.mul_inv, Matrix.one_mul, Matrix.mul_one]
  rw [hX] at h
  exact h.symm

private theorem orbitDerivativeWord_translate (f : P) (g x : G) (Xs : List Mat) :
    (orbitDerivativeWord r ds Xs (translate r ds g f) : G → ℂ) x =
      (orbitDerivativeWord r ds (Xs.map (adjDir r g)) f : G → ℂ) (x * g) := by
  induction Xs generalizing x with
  | nil => rfl
  | cons X Xs ih =>
    have heq : orbitDerivativeWord r ds Xs (translate r ds g f) =
        translate r ds g (orbitDerivativeWord r ds (Xs.map (adjDir r g)) f) :=
      Subtype.ext (funext ih)
    change (orbitDerivative r ds X (orbitDerivativeWord r ds Xs (translate r ds g f)) : G → ℂ) x = _
    rw [heq, orbitDerivative_translate]
    rfl

open scoped Matrix.Norms.Frobenius in
private theorem adjDir_entry_bound (X : Mat) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : G, ∀ i j, ‖adjDir r g X i j‖ ≤ C * realMatrixHeight g := by
  refine ⟨‖X‖, norm_nonneg _, fun g i j => ?_⟩
  have he : ‖(g⁻¹).val‖ * ‖g.val‖ ≤ realMatrixHeight g := by
    rw [realMatrixHeight_eq_frobenius]
    nlinarith [sq_nonneg (‖(g⁻¹).val‖ - ‖g.val‖), sq_nonneg ‖g.val‖, sq_nonneg ‖(g⁻¹).val‖]
  let A := adjDir r g X
  calc
    ‖A i j‖ ≤ ‖A‖ := (PiLp.norm_apply_le (WithLp.toLp 2 (A i)) j).trans
      (PiLp.norm_apply_le (WithLp.toLp 2 (fun k => WithLp.toLp 2 (A k))) i)
    _ ≤ ‖(g⁻¹).val‖ * ‖X‖ * ‖g.val‖ := (Matrix.frobenius_norm_mul ((g⁻¹).val * X) g.val).trans
      (mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul _ _) (norm_nonneg _))
    _ = ‖X‖ * (‖(g⁻¹).val‖ * ‖g.val‖) := by ring
    _ ≤ ‖X‖ * realMatrixHeight g := mul_le_mul_of_nonneg_left he (norm_nonneg _)

private theorem orbitDerivative_basis_sum (X : Mat) (f : P) :
    orbitDerivative r ds X f =
      ∑ ij : I × I, X ij.1 ij.2 • orbitDerivative r ds (Matrix.single ij.1 ij.2 1) f := by
  classical
  have hX : X = ∑ ij : I × I, X ij.1 ij.2 • Matrix.single ij.1 ij.2 1 := by
    rw [Fintype.sum_prod_type]
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
    exact Matrix.matrix_eq_sum_single X
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]
  change D X (f : G → ℂ) = ∑ ij : I × I, X ij.1 ij.2 • D (Matrix.single ij.1 ij.2 1) (f : G → ℂ)
  conv_lhs => rw [hX]
  exact rightDerivative_sum_smul _ _ _ _

private theorem orbitWord_append_sum (Xs : List Mat) (X : Mat) (f : P) (g x : G) :
    orbitWord r ds (Xs ++ [X]) f g x =
      ∑ ij : I × I, adjDir r g X ij.1 ij.2 •
        orbitWord r ds Xs (orbitDerivative r ds (Matrix.single ij.1 ij.2 1) f) g x := by
  simp only [orbitWord, ← orbitDerivativeWord_apply]
  rw [orbitDerivativeWord_translate r ds f g x (Xs ++ [X]), List.map_append,
    List.map_singleton, orbitDerivativeWord_append_singleton, orbitDerivative_basis_sum]
  simp only [map_sum, LinearMap.map_smul_of_tower, Submodule.coe_sum, Submodule.coe_smul_of_tower,
    Finset.sum_apply, Pi.smul_apply, orbitDerivativeWord_translate]

/-- The orbit-word evaluation is continuous jointly in the translation and evaluation points. -/
theorem continuous_orbitWord (Xs : List Mat) (f : P) :
    Continuous (fun p : G × G => orbitWord r ds Xs f p.1 p.2) := by
  induction Xs using List.reverseRecOn generalizing f with
  | nil =>
    simp only [orbitWord_nil]
    exact f.2.1.continuous.comp (continuous_snd.mul continuous_fst)
  | append_singleton Xs X ih =>
    simp only [orbitWord_append_sum]
    apply continuous_finsetSum _ fun ij _ => ?_
    have hA : Continuous (fun p : G × G => adjDir r p.1 X) :=
      ((Units.continuous_coe_inv.comp continuous_fst).matrix_mul continuous_const).matrix_mul
        (Units.continuous_val.comp continuous_fst)
    exact ((hA.matrix_elem ij.1 ij.2).smul (ih _))

/-- A common height exponent bounds the evaluation-side growth of all translated words;
on the translation side, adjoining one direction costs at most one height power. -/
theorem exists_uniform_orbitWord_height :
    ∃ N : ℕ, ∀ (Xs : List Mat) (f : P), ∃ C : ℝ, 0 ≤ C ∧ ∀ (g x : G),
      ‖orbitWord r ds Xs f g x‖ ≤ C * realMatrixHeight x ^ N * realMatrixHeight g ^ (N + Xs.length) := by
  obtain ⟨N, hN⟩ := exists_uniform_principalSeries_derivative_height r ds
  refine ⟨N, ?_⟩
  intro Xs
  induction Xs using List.reverseRecOn with
  | nil =>
    intro f
    obtain ⟨C, hC, hb⟩ := hN f f.2 []
    refine ⟨C, hC, fun g x => ?_⟩
    simp only [orbitWord_nil, List.length_nil, add_zero]
    calc
      _ ≤ C * realMatrixHeight (x * g) ^ N := hb (x * g)
      _ ≤ C * (realMatrixHeight x * realMatrixHeight g) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (realMatrixHeight_nonneg _) (realMatrixHeight_mul_le x g) _) hC
      _ = _ := by rw [mul_pow, ← mul_assoc]
  | append_singleton Xs X ih =>
    intro f
    classical
    let f' (ij : I × I) := orbitDerivative r ds (Matrix.single ij.1 ij.2 1) f
    choose C hC hb using fun ij => ih (f' ij)
    obtain ⟨A, hA, hAdj⟩ := adjDir_entry_bound r X
    refine ⟨A * ∑ ij, C ij, mul_nonneg hA (Finset.sum_nonneg fun ij _ => hC ij), fun g x => ?_⟩
    rw [orbitWord_append_sum]
    have hg := realMatrixHeight_nonneg g
    have hx := realMatrixHeight_nonneg x
    calc
      _ ≤ ∑ ij : I × I, (A * realMatrixHeight g) *
          (C ij * realMatrixHeight x ^ N * realMatrixHeight g ^ (N + Xs.length)) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ij _ => ?_)
        rw [norm_smul]
        exact mul_le_mul (hAdj g ij.1 ij.2) (hb ij g x) (norm_nonneg _)
          (mul_nonneg hA hg)
      _ = _ := by
        simp only [List.length_append, List.length_singleton, ← Nat.add_assoc, pow_succ]
        rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.sum_mul]
        ring

/-- Joint continuity and uniform polynomial bounds for all words of a real position-principal-
series orbit, with separate powers for translation and evaluation. -/
def RealPrincipalSeriesOrbitWordStatement : Prop :=
  (∀ (Xs : List Mat) (f : P), Continuous (fun p : G × G => orbitWord r ds Xs f p.1 p.2)) ∧
  (∃ N : ℕ, ∀ (Xs : List Mat) (f : P), ∃ C : ℝ, 0 ≤ C ∧ ∀ (g x : G),
    ‖orbitWord r ds Xs f g x‖ ≤ C * realMatrixHeight x ^ N * realMatrixHeight g ^ (N + Xs.length))

theorem realPrincipalSeriesOrbitWord : RealPrincipalSeriesOrbitWordStatement r ds :=
  ⟨continuous_orbitWord r ds, exists_uniform_orbitWord_height r ds⟩

end RealPrincipalSeries
end Langlands.Global.RankinSelbergGlobal
