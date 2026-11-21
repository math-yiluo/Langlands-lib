import Langlands.Automorphic.CuspidalAdmissible.CentralEigen
import Langlands.Global.RankinSelberg.RealParameterDeterminant
import Langlands.Global.RankinSelberg.RealUniformWhittakerModel
import Langlands.Representation.Archimedean.RealInductionStagesFourier
import Langlands.Representation.Archimedean.RealStandardCentralExponent

/-! # Scalar covariance of the real uniform coefficient space -/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.GramFormula (realPositionExponent)

private def expUnit (x : ℝ) : ℝˣ := Units.mk0 (Real.exp x) (Real.exp_pos x).ne'

private theorem inducedDeterminant_exp (d : ComplexCharacterData) (x : ℝ) :
    (d.realInducedDeterminant (expUnit x) : ℂ) = Complex.exp (2 * d.exponent * x) := by
  have hx := Real.exp_pos x
  have hz : ((realToComplex (expUnit x) : ℂˣ) : ℂ) = (Real.exp x : ℂ) := rfl
  rw [ComplexCharacterData.coe_realInducedDeterminant, d.character_eq, hz]
  change (((Real.exp x / |Real.exp x| : ℝ) : ℂ) *
    (((Real.exp x : ℂ) / (‖(Real.exp x : ℂ)‖ : ℂ)) ^ d.weight *
      (‖(Real.exp x : ℂ)‖ : ℂ) ^ (2 * d.exponent))) = _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx,
    div_self hx.ne', Complex.ofReal_one, div_self (by exact_mod_cast hx.ne' : (Real.exp x : ℂ) ≠ 0),
    one_zpow, one_mul, one_mul, RealPrincipalSeriesDuality.ofReal_exp_cpow, mul_comm]

private theorem determinant_exp (ds : List RealBlock) (x : ℝ) :
    (determinant ds (expUnit x) : ℂ) =
      Complex.exp (realStandardCentralExponent (realRank ds) ds * x) := by
  unfold realStandardCentralExponent
  induction ds with
  | nil => simp [determinant]
  | cons d ds ih =>
    cases d with
    | character c =>
      rw [realRank_cons, RealBlock.rank, Nat.one_add, Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, realPositionExponent]
      change (c.character (expUnit x) : ℂ) * (determinant ds (expUnit x) : ℂ) = _
      have hc : (c.character (expUnit x) : ℂ) = Complex.exp (c.exponent * x) :=
        InductionStages.realPositionCharacter_exp (.character c :: ds) 0 x
      rw [hc, ih, ← Complex.exp_add, add_mul]
    | induced c =>
      rw [realRank_cons, RealBlock.rank, show 2 + realRank ds = (realRank ds).succ.succ by omega,
        Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [Fin.val_zero, Fin.val_succ, realPositionExponent]
      change (c.realInducedDeterminant (expUnit x) : ℂ) * (determinant ds (expUnit x) : ℂ) = _
      rw [inducedDeterminant_exp, ih, ← Complex.exp_add]
      congr 1
      ring

private theorem determinant_neg (ds : List RealBlock) (z : ℝˣ) :
    determinant ds (-z) = determinant ds (-1) * determinant ds z := by
  induction ds with
  | nil => simp [determinant]
  | cons d ds ih =>
    change d.determinant (-z) * determinant ds (-z) =
      (d.determinant (-1) * determinant ds (-1)) * (d.determinant z * determinant ds z)
    rw [block_determinant_neg, ih]
    ac_rfl

private theorem matrixExpUnit_identity (n : ℕ) (x : ℝ) :
    matrixExpUnit n (x • (1 : Matrix (Fin n) (Fin n) ℝ)) =
      (GeneralLinear.scalar (expUnit x) : Langlands.GeneralLinear n ℝ) := by
  rw [show x • (1 : Matrix (Fin n) (Fin n) ℝ) = Matrix.diagonal (fun _ => x) by
    ext i j
    by_cases h : i = j <;> simp [h]]
  rw [RealPrincipalSeriesDuality.matrixExpUnit_diagonal]
  rfl

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ

private theorem coefficient_mul_exp {ds : List RealBlock} {a : ℝˣ}
    {B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ] (G → ℂ)}
    (hds : realRank ds = r + 1) (hB : IsRealWhittakerIntertwiner r ds a B)
    (f : Automorphic.realStandardKFinite (r + 1) ds) (g : G) (x : ℝ) :
    B f (g * GeneralLinear.scalar (expUnit x)) = (determinant ds (expUnit x) : ℂ) * B f g := by
  let lam := realStandardCentralExponent (r + 1) ds
  let X : M := 1
  let P (t : ℝ) := g * matrixExpUnit (r + 1) (t • X)
  have hR (k : G) : rightDerivative (matrixModel ℝ (r + 1)) X (B f) k = lam * B f k := by
    have hF := hB.2.2.2.2 X f (realStandardLie (r + 1) ds (1 ⊗ₜ[ℝ] X) f)
      (realStandardLie_one_tmul_apply_coe (r + 1) ds X f)
    rw [show X = 1 from rfl, realStandardLie_identity, map_smul] at hF
    exact (congrFun hF k).symm
  have hd (t : ℝ) : HasDerivAt (fun s => B f (P s)) (lam * B f (P t)) t := by
    have h := (differentiableAt_unitsExtension (hB.2.1 f)
      (Units.isUnit (P t))).hasFDerivAt
    have hval (s : ℝ) : (P s).val = g.val * NormedSpace.exp (s • X) := rfl
    have hP : HasDerivAt (fun s => (P s).val) ((P t).val * X) t := by
      simp_rw [hval]
      simpa only [Matrix.mul_assoc] using (hasDerivAt_exp_smul_const X t).const_mul g.val
    have hc := h.comp_hasDerivAt t hP
    rw [← rightDerivative_eq_fderiv (hB.2.1 f), hR] at hc
    simpa only [Function.comp_def, unitsExtension_val] using hc
  have h := Automorphic.OperatorRealization.eq_exp_mul_of_hasDerivAt hd x
  dsimp only [P, X, lam] at h
  rw [zero_smul, matrixExpUnit_zero, mul_one, matrixExpUnit_identity] at h
  rw [determinant_exp, hds]
  exact h

private theorem coefficient_mul_minusOne {ds : List RealBlock} {a : ℝˣ}
    {B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ] (G → ℂ)}
    (hds : realRank ds = r + 1) (hB : IsRealWhittakerIntertwiner r ds a B)
    (f : Automorphic.realStandardKFinite (r + 1) ds) (g : G) :
    B f (g * -1) = (determinant ds (-1) : ℂ) * B f g := by
  let k : unitaryCompact ℝ (r + 1) := ⟨-1, (-1 : Matrix.unitaryGroup (Fin (r + 1)) ℝ).property⟩
  have h := hB.2.2.2.1 k f ((determinant ds (-1) : ℂ) • f)
    (funext fun y => (standard_mul_minusOne ds hds f y).symm)
  rw [map_smul] at h
  exact (congrFun h g).symm

private theorem coefficient_mul_scalar {ds : List RealBlock} {a : ℝˣ}
    {B : Automorphic.realStandardKFinite (r + 1) ds →ₗ[ℂ] (G → ℂ)}
    (hds : realRank ds = r + 1) (hB : IsRealWhittakerIntertwiner r ds a B)
    (f : Automorphic.realStandardKFinite (r + 1) ds) (g : G) (z : ℝˣ) :
    B f (g * GeneralLinear.scalar z) = (determinant ds z : ℂ) * B f g := by
  have hp (y : ℝˣ) (hy : 0 < (y : ℝ)) : expUnit (Real.log (y : ℝ)) = y :=
    Units.ext (Real.exp_log hy)
  rcases lt_or_gt_of_ne z.ne_zero with hneg | hpos
  · have hpos : 0 < ((-z : ℝˣ) : ℝ) := by simpa only [Units.val_neg, neg_pos] using hneg
    have h := coefficient_mul_exp hds hB f g (Real.log ((-z : ℝˣ) : ℝ))
    rw [hp (-z) hpos] at h
    have hz : GeneralLinear.scalar z = (GeneralLinear.scalar (-z) : G) * -1 := by
      have hs : (GeneralLinear.scalar (-1 : ℝˣ) : G) = -1 := by
        apply Units.ext
        simp [GeneralLinear.scalar, Matrix.GeneralLinearGroup.coe_scalar, ← Matrix.diagonal_neg,
          Matrix.diagonal_one]
      rw [← hs, ← map_mul, mul_neg_one, neg_neg]
    rw [hz, ← mul_assoc, coefficient_mul_minusOne hds hB, h,
      ← mul_assoc, ← Units.val_mul, ← determinant_neg, neg_neg]
  · have h := coefficient_mul_exp hds hB f g (Real.log (z : ℝ))
    rwa [hp z hpos] at h

/-- Scalar covariance for the span of the specified moderate-growth coefficient maps. -/
def RealUniformWhittakerCentralCharacterStatement : Prop :=
  ∀ (r : ℕ) (ds : List RealBlock), realRank ds = r + 1 → ∀ (a : ℝˣ)
    (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ), W ∈ realUniformWhittakerModel r ds a →
      ∀ (z : ℝˣ) (g : Langlands.GeneralLinear (r + 1) ℝ),
        W (g * GeneralLinear.scalar z) = (determinant ds z : ℂ) * W g

theorem realUniformWhittakerCentralCharacter : RealUniformWhittakerCentralCharacterStatement := by
  intro r ds hds a W hW z g
  let L : (Langlands.GeneralLinear (r + 1) ℝ → ℂ) →ₗ[ℂ] ℂ :=
    LinearMap.proj (g * GeneralLinear.scalar z) - (determinant ds z : ℂ) • LinearMap.proj g
  have hle : realUniformWhittakerModel r ds a ≤ LinearMap.ker L := by
    refine iSup₂_le fun B hB => ?_
    rintro _ ⟨f, rfl⟩
    exact sub_eq_zero.mpr (coefficient_mul_scalar hds hB.1 f g z)
  exact sub_eq_zero.mp (hle hW)

end Langlands.Global.RankinSelbergGlobal.RealJacquet
