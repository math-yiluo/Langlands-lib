import Langlands.Global.RankinSelberg.ComplexLocalEqualTorusBoxes
import Langlands.Representation.Archimedean.ComplexBlockPolynomial

/-! # The simple-root differential equation for complex Whittaker coefficients -/

noncomputable section

open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexLocalConvergence

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open BlockPolynomial (rootUnit)
open ComplexCharacterChange (model_unipotent_mul)

variable {r : ℕ}

local notation "I" => Fin (r + 1)
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "N" => GeneralLinear.upperUnipotent (r + 1) ℂ
local notation "M" => Matrix I I ℂ
local notation "K" => unitaryCompact ℂ (r + 1)

private def simpleRoot (i : Fin r) (z : ℂ) : G :=
  rootUnit (ne_of_gt i.castSucc_lt_succ) z

private theorem simpleRoot_mem (i : Fin r) (z : ℂ) : simpleRoot i z ∈ N := by
  refine ⟨fun j l hjl => ?_, fun j => ?_⟩
  · change (1 + Matrix.single i.castSucc i.succ z : M) j l = 0
    have hne : j ≠ l := ne_of_gt (show l < j from hjl)
    simp only [Matrix.add_apply, Matrix.one_apply_ne hne, Matrix.single_apply, zero_add]
    rw [ite_eq_right_iff]
    rintro ⟨rfl, rfl⟩
    exact (not_lt_of_ge i.castSucc_lt_succ.le hjl).elim
  · change (1 + Matrix.single i.castSucc i.succ z : M) j j = 1
    simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply, add_eq_left]
    rw [ite_eq_right_iff]
    rintro ⟨rfl, hj⟩
    exact (ne_of_gt i.castSucc_lt_succ hj).elim

private theorem simpleRoot_sum (i : Fin r) (z : ℂ) :
    (∑ j : Fin r, (simpleRoot i z).val j.castSucc j.succ) = z := by
  have hentry (j : Fin r) :
      (simpleRoot i z).val j.castSucc j.succ = if j = i then z else 0 := by
    change (1 + Matrix.single i.castSucc i.succ z : M) j.castSucc j.succ = _
    simp only [Matrix.add_apply, Matrix.one_apply_ne (ne_of_lt j.castSucc_lt_succ),
      Matrix.single_apply, zero_add, Fin.castSucc_inj, Fin.succ_inj, and_self]
    by_cases h : i = j
    · subst j
      rfl
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
  simp_rw [hentry]
  simp

/-- The tangent direction of the real path in the simple-root subgroup whose
parameter in the trace character is real. -/
def simpleRootDirection (a : ℂˣ) (i : Fin r) : M :=
  Matrix.single i.castSucc i.succ ((a : ℂ)⁻¹)

private theorem simpleRoot_realPath (a : ℂˣ) (i : Fin r) (t : ℝ) :
    (simpleRoot i ((t : ℂ) * (a : ℂ)⁻¹)).val = 1 + t • simpleRootDirection a i := by
  change 1 + Matrix.single i.castSucc i.succ ((t : ℂ) * (a : ℂ)⁻¹) = _
  congr 1
  ext j l
  simp only [simpleRootDirection, Matrix.single_apply, Matrix.smul_apply]
  split <;> simp [Complex.real_smul]

/-- The nonzero derivative of the positive trace character on real parameters. -/
def rootCharacterDerivative : ℂ :=
  ((4 * Real.pi : ℝ) : ℂ) * Complex.I

theorem rootCharacterDerivative_ne_zero : rootCharacterDerivative ≠ 0 := by
  refine mul_ne_zero ?_ Complex.I_ne_zero
  exact_mod_cast mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) Real.pi_ne_zero

private theorem simpleRoot_traceCharacter (a : ℂˣ) (i : Fin r) (t : ℝ) :
    complexWhittakerCharacter a (simpleRoot i ((t : ℂ) * (a : ℂ)⁻¹)) =
      Complex.exp ((t : ℂ) * rootCharacterDerivative) := by
  unfold complexWhittakerCharacter
  rw [simpleRoot_sum]
  change (complexScaledCharacter a ((t : ℂ) * (a : ℂ)⁻¹) : ℂ) = _
  rw [complexScaledCharacter_apply, mul_left_comm, mul_inv_cancel₀ a.ne_zero, mul_one,
    Algebra.trace_complex_apply, Complex.ofReal_re, Real.fourierChar_apply]
  congr 1
  push_cast
  unfold rootCharacterDerivative
  push_cast
  ring

/-- Differentiation in the right direction obtained by conjugating the
simple-root direction by `g⁻¹` gives the left Whittaker eigenvalue. -/
theorem rightDerivative_conj_simpleRoot {ds : List ComplexCharacterData} {a : ℂˣ}
    {W : G → ℂ} (hW : W ∈ complexWhittakerModel r ds a)
    (hSm : ContMDiff (matrixModel ℂ (r + 1)) 𝓘(ℝ, ℂ) ∞ W) (i : Fin r) (g : G) :
    rightDerivative (matrixModel ℂ (r + 1))
        ((g⁻¹).val * simpleRootDirection a i * g.val) W g =
      rootCharacterDerivative * W g := by
  let X := simpleRootDirection a i
  let P (t : ℝ) := simpleRoot i ((t : ℂ) * (a : ℂ)⁻¹) * g
  have hp (t : ℝ) : (P t).val = (1 + t • X) * g.val := by
    simp only [P, Units.val_mul, simpleRoot_realPath, X]
  have hp₀ : (P 0).val = g.val := by simp [hp]
  have hPath : HasDerivAt (fun t => (P t).val) (X * g.val) 0 := by
    simp_rw [hp]
    simpa only [one_smul, id] using
      (((hasDerivAt_id (0 : ℝ)).smul_const X).const_add 1).mul_const g.val
  have hF : HasDerivAt (fun t => W (P t))
      (fderiv ℝ (unitsExtension W) g.val (X * g.val)) 0 := by
    have hd := (differentiableAt_unitsExtension hSm g.isUnit).hasFDerivAt
    rw [← hp₀] at hd
    simpa only [Function.comp_def, unitsExtension_val, hp₀] using
      hd.comp_hasDerivAt (0 : ℝ) hPath
  have hE (t : ℝ) : W (P t) = Complex.exp ((t : ℂ) * rootCharacterDerivative) * W g := by
    dsimp [P]
    rw [model_unipotent_mul hW ⟨_, simpleRoot_mem _ _⟩, simpleRoot_traceCharacter]
  have hC : HasDerivAt (fun t => W (P t)) (rootCharacterDerivative * W g) 0 := by
    simp_rw [hE]
    simpa [Complex.exp_eq_exp_ℂ, Complex.real_smul] using
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) rootCharacterDerivative (0 : ℝ)).mul_const (W g)
  rw [rightDerivative_eq_fderiv hSm]
  change fderiv ℝ (unitsExtension W) g.val (g.val * ((g⁻¹).val * X * g.val)) = _
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, show g.val * (g⁻¹).val = 1 from g.val_inv,
    Matrix.one_mul]
  exact hF.unique hC

private theorem diagonal_conj_rootDirection (x : I → ℝ) (a : ℂˣ) (i : Fin r) :
    ((expDiagonal x)⁻¹).val * simpleRootDirection a i * (expDiagonal x).val =
      (Real.exp (x i.castSucc - x i.succ))⁻¹ • simpleRootDirection a i := by
  rw [← expDiagonal_neg]
  ext j l
  simp only [expDiagonal_val, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply,
    Pi.neg_apply, simpleRootDirection, Matrix.single_apply]
  split
  · rename_i h
    rcases h with ⟨rfl, rfl⟩
    simp only [Complex.real_smul]
    have hscale : Real.exp (-x i.castSucc) * Real.exp (x i.succ) =
        (Real.exp (x i.castSucc - x i.succ))⁻¹ := by
      rw [← Real.exp_add, ← Real.exp_neg]
      congr 1
      ring
    calc
      _ = ((Real.exp (-x i.castSucc) : ℂ) * (Real.exp (x i.succ) : ℂ)) *
          (a : ℂ)⁻¹ := by ring
      _ = _ := by rw [← Complex.ofReal_mul, hscale]
  · simp

/-- On the positive diagonal and right unitary factor, a simple-root derivative
multiplies the coefficient by the real ratio of the adjacent diagonal entries
and the trace character derivative. -/
theorem rightDerivative_torus_simpleRoot {ds : List ComplexCharacterData} {a : ℂˣ}
    {W : G → ℂ} (hW : W ∈ complexWhittakerModel r ds a)
    (hSm : ContMDiff (matrixModel ℂ (r + 1)) 𝓘(ℝ, ℂ) ∞ W)
    (i : Fin r) (x : I → ℝ) (k : K) :
    rightDerivative (matrixModel ℂ (r + 1))
        ((k.val⁻¹).val * simpleRootDirection a i * k.val.val) W (expDiagonal x * k.val) =
      (Real.exp (x i.castSucc - x i.succ) : ℂ) * rootCharacterDerivative *
        W (expDiagonal x * k.val) := by
  let d := expDiagonal x
  let g := d * k.val
  let X := simpleRootDirection a i
  let Y := (k.val⁻¹).val * X * k.val.val
  let c := Real.exp (x i.castSucc - x i.succ)
  have hdir : (g⁻¹).val * X * g.val = c⁻¹ • Y := by
    change ((d * k.val)⁻¹).val * X * (d * k.val).val = _
    rw [mul_inv_rev, Units.val_mul, Units.val_mul]
    calc
      _ = (k.val⁻¹).val * (d⁻¹).val * X * d.val * k.val.val := by simp only [Matrix.mul_assoc]
      _ = (k.val⁻¹).val * ((d⁻¹).val * X * d.val) * k.val.val := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [show (d⁻¹).val * X * d.val = c⁻¹ • X from diagonal_conj_rootDirection x a i]
        simp only [Y, Matrix.mul_smul, Matrix.smul_mul]
  have he := rightDerivative_conj_simpleRoot hW hSm i g
  rw [hdir, rightDerivative_eq_fderiv hSm, Matrix.mul_smul, map_smul, Complex.real_smul,
    Complex.ofReal_inv] at he
  rw [rightDerivative_eq_fderiv hSm]
  change (fderiv ℝ (unitsExtension W) g.val) (g.val * Y) = (c : ℂ) * rootCharacterDerivative * W g
  have hc : (c : ℂ) ≠ 0 := by exact_mod_cast Real.exp_ne_zero (x i.castSucc - x i.succ)
  have h := congrArg ((c : ℂ) * ·) he
  simpa only [← mul_assoc, mul_inv_cancel₀ hc, one_mul] using h

/-- One right derivative of a `U(n)`-finite standard vector. -/
def standardDerivative {ds : List ComplexCharacterData} (X : M)
    (f : Automorphic.complexStandardKFinite (r + 1) ds) :
    Automorphic.complexStandardKFinite (r + 1) ds :=
  ⟨rightDerivative (matrixModel ℂ (r + 1)) X f,
    rightDerivative_mem_kFiniteFunctions_complexStandardModule (r + 1) ds f.property X⟩

/-- Successive right derivatives of a standard vector, with the first direction
in the list acting on the result for the tail. -/
def standardDerivativeWord {ds : List ComplexCharacterData} (word : List M)
    (f : Automorphic.complexStandardKFinite (r + 1) ds) :
    Automorphic.complexStandardKFinite (r + 1) ds :=
  word.foldr standardDerivative f

/-- The simple-root derivative word conjugated into the right frame of `k`. -/
def simpleRootStandardWord {ds : List ComplexCharacterData} (a : ℂˣ) (k : K)
    (word : List (Fin r)) (f : Automorphic.complexStandardKFinite (r + 1) ds) :
    Automorphic.complexStandardKFinite (r + 1) ds :=
  standardDerivativeWord (word.map fun i =>
    (k.val⁻¹).val * simpleRootDirection a i * k.val.val) f

/-- The product of the simple-root character multipliers is realized by the
corresponding derivative word on the inducing vector. -/
theorem intertwiner_simpleRootWord {ds : List ComplexCharacterData} {a : ℂˣ}
    {B : Automorphic.complexStandardKFinite (r + 1) ds →ₗ[ℂ] (G → ℂ)}
    (hB : IsComplexWhittakerIntertwiner r ds a B)
    (f : Automorphic.complexStandardKFinite (r + 1) ds)
    (word : List (Fin r)) (x : I → ℝ) (k : K) :
    B (simpleRootStandardWord a k word f) (expDiagonal x * k.val) =
      (word.map fun i => (Real.exp (x i.castSucc - x i.succ) : ℂ) *
        rootCharacterDerivative).prod * B f (expDiagonal x * k.val) := by
  let Y (i : Fin r) := (k.val⁻¹).val * simpleRootDirection a i * k.val.val
  let weight (i : Fin r) := (Real.exp (x i.castSucc - x i.succ) : ℂ) * rootCharacterDerivative
  let g := expDiagonal x * k.val
  change B (standardDerivativeWord (word.map Y) f) g = (word.map weight).prod * B f g
  induction word with
  | nil => simp [standardDerivativeWord]
  | cons i word ih =>
    let v := standardDerivativeWord (word.map Y) f
    have hmem : B v ∈ complexWhittakerModel r ds a :=
      (le_iSup₂ (f := fun A (_ : IsComplexWhittakerIntertwiner r ds a A) =>
        LinearMap.range A) B hB) ⟨v, rfl⟩
    change B (standardDerivative (Y i) v) g = weight i * (word.map weight).prod * B f g
    have hder := congrFun (hB.2.2.2.2 (Y i) v (standardDerivative (Y i) v) rfl) g
    rw [hder, rightDerivative_torus_simpleRoot hmem (hB.2.1 v) i x k]
    change weight i * B (standardDerivativeWord (word.map Y) f) g = _
    rw [ih]
    simp only [weight, mul_assoc]

end Langlands.Global.RankinSelbergGlobal.ComplexLocalConvergence
