import Langlands.Representation.Shahidi.OpenCellBaseValues

/-! # The open-cell integral for the `(1, n)` parabolic

For `ψ` of conductor `𝒪`, every function `Ψ` of Whittaker type on `GL_(t+1)` and every `d ∈ ℤ`,
the integral `∫ F_(d,Ψ)(lower Y) conj ψ(Y_last) dY`, where `F_(d,Ψ)` is the lift of the shell
function `Φ_(d,Ψ)`, is `0` for `d < 0` and for `d > t + 1`, and for `0 ≤ d ≤ t + 1`, writing
`D = d.toNat`, it is

`(-1)^D q^(α(t+1,D)) Ψ(ϖ^(κ(t,D)))`,

where `α(n, D) = ∑_(j<D) (n-1-j)` and `κ(t, D) = baseKappa t D = (0, …, 0, -1, …, -1)` with
`min(D, t+1)` last entries equal to `-1` (here `D ≤ t + 1`, so there are `D` of them).
The proof is by induction on `t`, peeling off the last entry of `Y`. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell.Base

open Langlands.GeneralLinear Langlands.Conductor MeasureTheory
open scoped NNReal

universe u

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}

local instance ocBaseIndTopology : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
local instance ocBaseIndValuativeRel : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance ocBaseIndLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField
local instance ocBaseIndT2 : T2Space K.Carrier := K.canonicalTopologicalData.fieldT2
local instance ocBaseIndSecondCountable : SecondCountableTopology K.Carrier :=
  K.canonicalTopologicalData.secondCountableTopology
local instance ocBaseIndMeasurable : MeasurableSpace K.Carrier := borel K.Carrier
local instance ocBaseIndBorel : BorelSpace K.Carrier := ⟨rfl⟩

/-- The exponent `κ(t, D) = (0, …, 0, -1, …, -1)` with `min(D, t + 1)` entries `-1` (the last
ones). -/
def baseKappa (t D : ℕ) : Fin (t + 1) → ℤ := fun i => if t + 1 ≤ (i : ℕ) + D then -1 else 0

/-- The exponent `α(n, d) = ∑_(j<d) (n - 1 - j)`. -/
def baseAlpha (n D : ℕ) : ℕ := ∑ j ∈ Finset.range D, (n - 1 - j)

theorem baseKappa_zero (t : ℕ) : baseKappa t 0 = fun _ => 0 := by
  funext i
  simp only [baseKappa, add_zero]
  rw [ite_eq_right]
  intro h
  have := i.isLt
  omega

theorem baseKappa_succ (t D : ℕ) :
    Fin.append (baseKappa t D) (fun _ : Fin 1 => (-1 : ℤ)) = baseKappa (t + 1) (D + 1) := by
  funext i
  refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
  · rw [Fin.append_left]
    simp only [baseKappa, Fin.val_castAdd]
    by_cases h : t + 1 ≤ (i' : ℕ) + D
    · rw [ite_eq_left h, ite_eq_left (by omega)]
    · rw [ite_eq_right h, ite_eq_right (by omega)]
  · rw [Fin.append_right]
    simp only [baseKappa, Fin.val_natAdd]
    rw [ite_eq_left (by omega)]

theorem baseAlpha_zero (n : ℕ) : baseAlpha n 0 = 0 := by
  simp [baseAlpha]

theorem baseAlpha_succ (t D : ℕ) : baseAlpha (t + 2) (D + 1) = (t + 1) + baseAlpha (t + 1) D := by
  simp only [baseAlpha]
  rw [Finset.sum_range_succ']
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  omega

variable (ϖ : K.Carrierˣ)

/-- The value of the open-cell integral for the `(1, t+1)` parabolic: `0` unless `0 ≤ d ≤ t + 1`,
and `(-1)^D q^(α(t+1, D)) Ψ(ϖ^(κ(t, D)))` with `D = d.toNat` in that range. -/
def baseValue (t : ℕ) (d : ℤ) (Ψ : Langlands.GeneralLinear (t + 1) K.Carrier → ℂ) : ℂ :=
  if 0 ≤ d ∧ d ≤ (t : ℤ) + 1 then
    (-1 : ℂ) ^ d.toNat * ((K.canonicalTopologicalData.residueCardinality : ℂ)) ^
      (baseAlpha (t + 1) d.toNat) * Ψ (Iwasawa.torus ϖ (baseKappa t d.toNat))
  else 0

theorem baseValue_of_neg {t : ℕ} {d : ℤ} (hd : d < 0) (Ψ : Langlands.GeneralLinear (t + 1) K.Carrier → ℂ) :
    baseValue ϖ t d Ψ = 0 := by
  rw [baseValue, ite_eq_right (fun h => by omega)]

variable {ϖ}

theorem twistOne_torus {t' : ℕ} (Ψ : Langlands.GeneralLinear ((t' + 1) + 1) K.Carrier → ℂ)
    (κ : Fin (t' + 1) → ℤ) :
    twistOne ϖ Ψ 1 (Iwasawa.torus ϖ κ) =
      Ψ (Iwasawa.torus ϖ (Fin.append κ (fun _ : Fin 1 => (-1 : ℤ)))) := by
  rw [twistOne, RankinSelberg.TwoBlockDominantRectangular.blockSum_torus]
  rfl

variable (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)
variable {ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _
  K.canonicalTopologicalData.topology}
variable (hψ : HasIntegerConductor ψ)

section Step

variable {t' : ℕ}

open Classical in
include hψ in
theorem inner_of_mem {d : ℤ} {Ψ : Langlands.GeneralLinear ((t' + 1) + 1) K.Carrier → ℂ}
    (hΨ : IsWhittakerType ψ Ψ) {c : K.Carrier} (hc : c ∈ K.canonicalTopologicalData.Integers) :
    ∫ y, baseIntegrand ψ hϖ d Ψ (joinColumn K (t' + 1) c y) ∂matrixHaar K (t' + 1) 1 =
      if d = 0 then Ψ 1 else 0 := by
  simp_rw [baseIntegrand_joinColumn_of_mem hϖ hψ hΨ hc]
  by_cases hd : d = 0
  · simp only [hd, true_and, ite_true]
    have hmeas : MeasurableSet (integralMatrices K (t' + 1) 1 :
        Set (Matrix (Fin (t' + 1)) (Fin 1) K.Carrier)) := (isOpen_integralMatrices K).measurableSet
    have e : (fun y : Matrix (Fin (t' + 1)) (Fin 1) K.Carrier =>
        if y ∈ integralMatrices K (t' + 1) 1 then Ψ 1 else 0) =
        (integralMatrices K (t' + 1) 1 : Set (Matrix (Fin (t' + 1)) (Fin 1) K.Carrier)).indicator
          (fun _ => Ψ 1) := by
      funext y
      simp [Set.indicator]
    rw [e, integral_indicator hmeas, setIntegral_const, measureReal_def,
      matrixHaar_integralMatrices, ENNReal.toReal_one, one_smul]
  · simp only [hd, false_and, ite_false, integral_zero]

include hϖ in
theorem inner_of_valuation {d : ℤ} {Ψ : Langlands.GeneralLinear ((t' + 1) + 1) K.Carrier → ℂ}
    (hΨ : IsWhittakerType ψ Ψ) {c : K.Carrier} {e : ℕ}
    (he : @ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel c =
      (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel (ϖ : K.Carrier)) ^
        (-(e : ℤ))) :
    ∫ y, baseIntegrand ψ hϖ d Ψ (joinColumn K (t' + 1) c y) ∂matrixHaar K (t' + 1) 1 =
      starRingEnd ℂ (ψ c : ℂ) *
        (((((K.canonicalTopologicalData.residueCardinality : ℝ) ^ (e : ℤ)) ^ ((t' + 1) * 1) : ℝ) :
          ℂ) * ∫ z, baseIntegrand ψ hϖ (d - e) (twistOne ϖ Ψ e) z ∂matrixHaar K (t' + 1) 1) := by
  set v := @ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel
  have hv0 : 0 < v (ϖ : K.Carrier) := Iwasawa.valuation_pos v ϖ
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero] at he
    exact (zpow_ne_zero _ hv0.ne') he.symm
  set uc : K.Carrierˣ := Units.mk0 c hc0
  have huc : ((uc⁻¹ : K.Carrierˣ) : K.Carrier) = c⁻¹ := by
    rw [Units.val_inv_eq_inv_val, Units.val_mk0]
  simp_rw [baseIntegrand_joinColumn_of_valuation hϖ hΨ he]
  rw [integral_const_mul]
  congr 1
  have h := integral_inv_smul K uc (fun z : Matrix (Fin (t' + 1)) (Fin 1) K.Carrier =>
    (ψ (z (Fin.last t') 0) : ℂ) *
      liftFunction hϖ (shellΦ (d - e) (twistOne ϖ Ψ e)) (lower (0 + 1) (t' + 1) K.Carrier z))
  simp only [huc] at h
  rw [h, normalizedAbs_of_valuation hϖ (u := uc) (by rw [Units.val_mk0]; exact he),
    integral_char_mul_liftFunction hϖ (isWhittakerType_twistOne hΨ e).2]

include hϖ hψ in
/-- **The induction step.** -/
theorem integral_baseIntegrand_succ
    (ih : ∀ (d : ℤ) (Ψ : Langlands.GeneralLinear (t' + 1) K.Carrier → ℂ), IsWhittakerType ψ Ψ →
      ∫ z, baseIntegrand ψ hϖ d Ψ z ∂matrixHaar K (t' + 1) 1 = baseValue ϖ t' d Ψ)
    (d : ℤ) {Ψ : Langlands.GeneralLinear ((t' + 1) + 1) K.Carrier → ℂ} (hΨ : IsWhittakerType ψ Ψ) :
    ∫ Y, baseIntegrand ψ hϖ d Ψ Y ∂matrixHaar K ((t' + 1) + 1) 1 = baseValue ϖ (t' + 1) d Ψ := by
  set q := (K.canonicalTopologicalData.residueCardinality : ℝ)
  set C : ℕ → ℂ := fun e => if e = 0 then (if d = 0 then Ψ 1 else 0) else
    ((((q ^ (e : ℤ)) ^ ((t' + 1) * 1) : ℝ) : ℂ) * baseValue ϖ t' (d - e) (twistOne ϖ Ψ e)) with hC
  rw [integral_column K (t' + 1) (integrable_baseIntegrand hϖ hψ hΨ.2)]
  rw [integral_outer K hϖ ψ hψ d.toNat C ?_ _ ?_ ?_]
  · -- the algebra
    simp only [hC, one_ne_zero, ite_false, ite_true, Nat.cast_one, zpow_one]
    by_cases hd0 : d < 0
    · rw [baseValue_of_neg ϖ hd0, baseValue_of_neg ϖ (by omega), ite_eq_right (by omega)]
      simp
    · by_cases hd1 : d = 0
      · subst hd1
        rw [baseValue_of_neg ϖ (by omega), ite_eq_left rfl, mul_zero, sub_zero, baseValue,
          ite_eq_left (by omega)]
        simp [baseKappa_zero, baseAlpha_zero, torus_const_zero]
      · rw [ite_eq_right hd1, zero_sub]
        obtain ⟨D, hD⟩ : ∃ D : ℕ, d = D + 1 := ⟨(d - 1).toNat, by omega⟩
        subst hD
        have hDd : (D : ℤ) + 1 - 1 = D := by ring
        simp only [baseValue, hDd]
        by_cases hDt : D ≤ t' + 1
        · rw [ite_eq_left (by omega), ite_eq_left (by omega)]
          have h1 : (((D : ℤ) + 1).toNat) = D + 1 := by omega
          have h2 : ((D : ℤ).toNat) = D := by omega
          rw [h1, h2, twistOne_torus, baseKappa_succ, baseAlpha_succ]
          simp only [q]
          push_cast
          ring
        · rw [ite_eq_right (by omega), ite_eq_right (by omega), mul_zero, neg_zero]
  · intro e he
    simp only [hC]
    rw [ite_eq_right (by omega), baseValue_of_neg ϖ (by omega), mul_zero]
  · intro c hc
    simp only [hC, ite_true]
    exact inner_of_mem hϖ hψ hΨ hc
  · intro c _ e he hv
    simp only [hC, ite_eq_right (show e ≠ 0 by omega)]
    rw [inner_of_valuation hϖ hΨ hv, ih (d - e) (twistOne ϖ Ψ e) (isWhittakerType_twistOne hΨ e)]

end Step

section GL2

theorem sum_fin_zero_one {M : Type*} [AddCommMonoid M] (f : Fin (0 + 1) → M) :
    ∑ i, f i = f 0 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]

/-- The first index of `Fin ((0+1)+(0+1))`. -/
abbrev i2a : Fin ((0 + 1) + (0 + 1)) := Fin.castAdd (0 + 1) 0

/-- The second index of `Fin ((0+1)+(0+1))`. -/
abbrev i2c : Fin ((0 + 1) + (0 + 1)) := Fin.natAdd (0 + 1) 0

theorem ext2 {M N : Matrix (Fin ((0 + 1) + (0 + 1))) (Fin ((0 + 1) + (0 + 1))) K.Carrier}
    (h1 : M i2a i2a = N i2a i2a) (h2 : M i2a i2c = N i2a i2c) (h3 : M i2c i2a = N i2c i2a)
    (h4 : M i2c i2c = N i2c i2c) : M = N := by
  ext i j
  induction i using Fin.addCases with
  | left i' =>
    induction j using Fin.addCases with
    | left j' => rw [zero_fin_one i', zero_fin_one j']; exact h1
    | right j' => rw [zero_fin_one i', zero_fin_one j']; exact h2
  | right i' =>
    induction j using Fin.addCases with
    | left j' => rw [zero_fin_one i', zero_fin_one j']; exact h3
    | right j' => rw [zero_fin_one i', zero_fin_one j']; exact h4

theorem mul_apply2 (M N : Matrix (Fin ((0 + 1) + (0 + 1))) (Fin ((0 + 1) + (0 + 1))) K.Carrier)
    (i j : Fin ((0 + 1) + (0 + 1))) : (M * N) i j = M i i2a * N i2a j + M i i2c * N i2c j := by
  rw [Matrix.mul_apply, Fin.sum_univ_add, sum_fin_zero_one, sum_fin_zero_one]

theorem i2a_ne_i2c : i2a ≠ i2c := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_zero] at this
  omega

/-- The matrix `[[0, -1], [1, y⁻¹]]`. -/
def k2Mat (y : K.Carrier) : Matrix (Fin ((0 + 1) + (0 + 1))) (Fin ((0 + 1) + (0 + 1))) K.Carrier :=
  Matrix.of fun i j => Fin.addCases (fun _ => Fin.addCases (fun _ => 0) (fun _ => -1) j)
    (fun _ => Fin.addCases (fun _ => 1) (fun _ => y⁻¹) j) i

/-- The matrix `[[y⁻¹, 1], [-1, 0]]`. -/
def k2InvMat (y : K.Carrier) : Matrix (Fin ((0 + 1) + (0 + 1))) (Fin ((0 + 1) + (0 + 1))) K.Carrier :=
  Matrix.of fun i j => Fin.addCases (fun _ => Fin.addCases (fun _ => y⁻¹) (fun _ => 1) j)
    (fun _ => Fin.addCases (fun _ => -1) (fun _ => 0) j) i

theorem k2Mat_mul_inv (y : K.Carrier) : k2Mat y * k2InvMat y = 1 := by
  apply ext2 <;>
    simp only [mul_apply2, k2Mat, k2InvMat, Matrix.of_apply, Fin.addCases_left,
      Fin.addCases_right, Matrix.one_apply, i2a_ne_i2c, i2a_ne_i2c.symm, ite_true, ite_false] <;>
    ring

theorem k2Mat_inv_mul (y : K.Carrier) : k2InvMat y * k2Mat y = 1 := by
  apply ext2 <;>
    simp only [mul_apply2, k2Mat, k2InvMat, Matrix.of_apply, Fin.addCases_left,
      Fin.addCases_right, Matrix.one_apply, i2a_ne_i2c, i2a_ne_i2c.symm, ite_true, ite_false] <;>
    ring

/-- `[[0, -1], [1, y⁻¹]]` as an invertible matrix. -/
def k2GL (y : K.Carrier) : Langlands.GeneralLinear ((0 + 1) + (0 + 1)) K.Carrier :=
  ⟨k2Mat y, k2InvMat y, k2Mat_mul_inv y, k2Mat_inv_mul y⟩

theorem k2GL_mem {y : K.Carrier} (hy : y⁻¹ ∈ K.canonicalTopologicalData.Integers) :
    k2GL y ∈ integralSubgroup K.canonicalTopologicalData.Integers (0 + 1 + 0) := by
  refine (mem_integralSubgroup _ _ _).2 ⟨fun i j => ?_, fun i j => ?_⟩
  · change k2Mat y i j ∈ _
    induction i using Fin.addCases <;> induction j using Fin.addCases <;>
      simp only [k2Mat, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]
    · exact zero_mem _
    · exact neg_mem (one_mem _)
    · exact one_mem _
    · exact hy
  · change k2InvMat y i j ∈ _
    induction i using Fin.addCases <;> induction j using Fin.addCases <;>
      simp only [k2InvMat, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right]
    · exact hy
    · exact one_mem _
    · exact neg_mem (one_mem _)
    · exact zero_mem _

theorem lower_eq_GL2 (Y : Matrix (Fin (0 + 1)) (Fin 1) K.Carrier) (hy : Y 0 0 ≠ 0) :
    lower (0 + 1) (0 + 1) K.Carrier Y =
      upper (0 + 1) (0 + 1) K.Carrier (Matrix.of fun _ _ => (Y 0 0)⁻¹) *
        GeneralLinear.blockSum (scalarGL (Units.mk0 _ hy)⁻¹, scalarGL (Units.mk0 _ hy)) *
        k2GL (Y 0 0) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  apply ext2 <;>
    simp only [mul_apply2, k2GL, k2Mat, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right,
      lower_first_first, lower_first_second, lower_second_first, lower_second_second,
      upper_first_first, upper_first_second, upper_second_first, upper_second_second,
      blockSum_apply_left, blockSum_apply_right, blockSum_apply_left_right,
      blockSum_apply_right_left, scalarGL, Iwasawa.diagonalUnits_val, Matrix.diagonal_apply_eq,
      ite_true, Units.val_inv_eq_inv_val, Units.val_mk0, Matrix.of_apply] <;>
    field_simp <;>
    ring

include hϖ in
theorem determinantNorm_scalarGL_inv {u : K.Carrierˣ} {e : ℕ}
    (hu : @ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel (u : K.Carrier) =
      (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel (ϖ : K.Carrier)) ^
        (-(e : ℤ))) :
    ((K.canonicalTopologicalData.determinantNorm (0 + 1) (scalarGL u⁻¹) : ℝ≥0) : ℝ) =
      (K.canonicalTopologicalData.residueCardinality : ℝ) ^ (-(e : ℤ)) := by
  rw [K.canonicalTopologicalData.determinantNorm_coe]
  change K.canonicalTopologicalData.normalizedAbs
    (((Iwasawa.diagonalUnits fun _ : Fin (0 + 1) => u⁻¹ : Langlands.GeneralLinear (0 + 1) K.Carrier) :
      Matrix (Fin (0 + 1)) (Fin (0 + 1)) K.Carrier)).det = _
  have hinv : K.canonicalTopologicalData.normalizedAbs ((u : K.Carrier)⁻¹) =
      (K.canonicalTopologicalData.normalizedAbs (u : K.Carrier))⁻¹ := by
    rw [← K.canonicalTopologicalData.normalizedAbsHom_coe,
      ← K.canonicalTopologicalData.normalizedAbsHom_coe, map_inv₀, NNReal.coe_inv]
  rw [Iwasawa.diagonalUnits_val, Matrix.det_diagonal, Fin.prod_univ_one, Units.val_inv_eq_inv_val,
    hinv, normalizedAbs_of_valuation hϖ hu, zpow_neg]

theorem scalarGL_eq_torus_mul {n : ℕ} {u w : K.Carrierˣ} {e : ℕ}
    (huw : (u : K.Carrier) = ((ϖ ^ (-(e : ℤ)) : K.Carrierˣ) : K.Carrier) * w) :
    (scalarGL u : Langlands.GeneralLinear n K.Carrier) =
      Iwasawa.torus ϖ (fun _ => -(e : ℤ)) * Iwasawa.diagonalUnits (fun _ : Fin n => w) := by
  rw [scalarGL, Iwasawa.torus, ← map_mul]
  congr 1
  funext i
  apply Units.ext
  rw [huw]
  rfl

theorem diagonalUnits_mem_of_valuation {n : ℕ} {w : K.Carrierˣ}
    (hw : @ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel (w : K.Carrier) = 1) :
    Iwasawa.diagonalUnits (fun _ : Fin (n + 1) => w) ∈
      integralSubgroup K.canonicalTopologicalData.Integers n :=
  Iwasawa.diagonalUnits_mem (v := @ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel)
    (fun _ : Fin (n + 1) => w) fun _ => hw

end GL2

section Base0

include hψ in
theorem baseIntegrand_GL2_of_mem {d : ℤ} {Ψ : Langlands.GeneralLinear (0 + 1) K.Carrier → ℂ}
    (hΨ : IsWhittakerType ψ Ψ) {Y : Matrix (Fin (0 + 1)) (Fin 1) K.Carrier}
    (hY : Y 0 0 ∈ K.canonicalTopologicalData.Integers) :
    baseIntegrand ψ hϖ d Ψ Y = if d = 0 then Ψ 1 else 0 := by
  have hYi : Y ∈ integralMatrices K (0 + 1) 1 := by
    refine (mem_integralMatrices_iff K _ _ Y).2 fun i j => ?_
    rw [zero_fin_one i, Subsingleton.elim j 0]
    exact hY
  have hΦ := isLeviInvariant_shellΦ (K := K) d hΨ.2
  have hk := lower_mem_integralSubgroup Y hYi
  unfold baseIntegrand
  rw [show lower (0 + 1) (0 + 1) K.Carrier Y = 1 * lower (0 + 1) (0 + 1) K.Carrier Y by
    rw [one_mul], liftFunction_mul_integral hϖ hΦ 1 _ hk, liftFunction_one hϖ hΦ]
  have hl : Y (Fin.last 0) 0 = Y 0 0 := rfl
  rw [hl, hψ.1 _ hY]
  simp only [shellΦ, map_one, Units.val_one, NNReal.coe_one]
  by_cases hd : d = 0
  · subst hd
    simp
  · rw [ite_eq_right (fun h => hd (by
      have := zpow_residue_injective (K := K) (a := 0) (b := -d) (by rw [zpow_zero]; exact h)
      omega)), ite_eq_right hd]
    simp

include hϖ in
theorem baseIntegrand_GL2_of_valuation {d : ℤ} {Ψ : Langlands.GeneralLinear (0 + 1) K.Carrier → ℂ}
    (hΨ : IsWhittakerType ψ Ψ) {Y : Matrix (Fin (0 + 1)) (Fin 1) K.Carrier} {e : ℕ}
    (hv : @ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel (Y 0 0) =
      (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel (ϖ : K.Carrier)) ^
        (-(e : ℤ))) :
    baseIntegrand ψ hϖ d Ψ Y = starRingEnd ℂ (ψ (Y 0 0) : ℂ) *
      (if d = e then Ψ (Iwasawa.torus ϖ (fun _ => -(e : ℤ))) else 0) := by
  set v := @ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel
  have hv0 : 0 < v (ϖ : K.Carrier) := Iwasawa.valuation_pos v ϖ
  have hy : Y 0 0 ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact (zpow_ne_zero _ hv0.ne') hv.symm
  have hyI : (Y 0 0)⁻¹ ∈ K.canonicalTopologicalData.Integers := by
    change v (Y 0 0)⁻¹ ≤ 1
    rw [map_inv₀, hv, ← zpow_neg, neg_neg]
    exact zpow_le_one₀ hv0 hϖ.1.le (by omega)
  have hΦ := isLeviInvariant_shellΦ (K := K) d hΨ.2
  set u : K.Carrierˣ := Units.mk0 _ hy
  have hu : v (u : K.Carrier) = v (ϖ : K.Carrier) ^ (-(e : ℤ)) := by rw [Units.val_mk0]; exact hv
  obtain ⟨w, hw, huw⟩ := exists_unit_of_valuation hu
  unfold baseIntegrand
  rw [lower_eq_GL2 Y hy, liftFunction_law hϖ hΦ _ _ _ _ (k2GL_mem hyI)]
  have hl : Y (Fin.last 0) 0 = Y 0 0 := rfl
  rw [hl, mul_comm]
  congr 1
  simp only [shellΦ]
  rw [determinantNorm_scalarGL_inv hϖ hu, scalarGL_eq_torus_mul huw,
    hΨ.2 _ _ (diagonalUnits_mem_of_valuation (n := 0) hw)]
  by_cases hde : d = e
  · rw [ite_eq_left (by rw [hde]), ite_eq_left hde]
  · rw [ite_eq_right (fun h => hde (by have := zpow_residue_injective (K := K) h; omega)),
      ite_eq_right hde]

include hϖ hψ in
/-- **The case `GL_2`.** -/
theorem integral_baseIntegrand_zero (d : ℤ) {Ψ : Langlands.GeneralLinear (0 + 1) K.Carrier → ℂ}
    (hΨ : IsWhittakerType ψ Ψ) :
    ∫ Y, baseIntegrand ψ hϖ d Ψ Y ∂matrixHaar K (0 + 1) 1 = baseValue ϖ 0 d Ψ := by
  set C : ℕ → ℂ := fun e => if e = 0 then (if d = 0 then Ψ 1 else 0) else
    (if d = e then Ψ (Iwasawa.torus ϖ (fun _ => -(e : ℤ))) else 0) with hC
  rw [integral_column K 0 (integrable_baseIntegrand hϖ hψ hΨ.2)]
  have hdirac : matrixHaar K 0 1 = Measure.dirac 0 :=
    RankinSelberg.rectangularMeasure_zero_rows _ _
  have hinner : ∀ c : K.Carrier, ∫ y, baseIntegrand ψ hϖ d Ψ (joinColumn K 0 c y) ∂matrixHaar K 0 1 =
      baseIntegrand ψ hϖ d Ψ (joinColumn K 0 c 0) := by
    intro c
    have hconst : ∀ y : Matrix (Fin 0) (Fin 1) K.Carrier, joinColumn K 0 c y = joinColumn K 0 c 0 :=
      fun y => by rw [Subsingleton.elim y 0]
    simp_rw [hconst]
    rw [hdirac, integral_const, Measure.dirac_real_apply_of_mem (Set.mem_univ _), one_smul]
  simp_rw [hinner]
  have hj : ∀ c : K.Carrier, joinColumn K 0 c 0 0 0 = c := fun c => joinColumn_last K 0 c 0 0
  rw [integral_outer K hϖ ψ hψ d.toNat C ?_ _ ?_ ?_]
  · simp only [hC, one_ne_zero, ite_false, ite_true, Nat.cast_one]
    by_cases hd0 : d < 0
    · rw [baseValue_of_neg ϖ hd0, ite_eq_right (by omega), ite_eq_right (by omega), sub_zero]
    · by_cases hd1 : d = 0
      · subst hd1
        rw [ite_eq_left rfl, ite_eq_right (by omega), sub_zero, baseValue, ite_eq_left (by omega)]
        simp [baseKappa_zero, baseAlpha_zero, torus_const_zero]
      · by_cases hd2 : d = 1
        · subst hd2
          rw [ite_eq_right hd1, ite_eq_left rfl, zero_sub, baseValue, ite_eq_left (by omega)]
          have h1 : (1 : ℤ).toNat = 1 := rfl
          have hk : baseKappa 0 1 = fun _ => -1 := by
            funext i
            simp [baseKappa]
          rw [h1, hk]
          simp [baseAlpha]
        · rw [ite_eq_right hd1, ite_eq_right hd2, sub_zero, baseValue, ite_eq_right (by omega)]
  · intro e he
    simp only [hC]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · intro c hc
    simp only [hC, ite_true]
    rw [baseIntegrand_GL2_of_mem hϖ hψ hΨ (by rw [hj]; exact hc)]
  · intro c _ e he hv
    simp only [hC, ite_eq_right (show e ≠ 0 by omega)]
    rw [baseIntegrand_GL2_of_valuation hϖ hΨ (by rw [hj]; exact hv), hj]

end Base0

include hϖ hψ in
/-- **The open-cell integral for the `(1, t+1)` parabolic.** -/
theorem integral_baseIntegrand (t : ℕ) (d : ℤ) {Ψ : Langlands.GeneralLinear (t + 1) K.Carrier → ℂ}
    (hΨ : IsWhittakerType ψ Ψ) :
    ∫ Y, baseIntegrand ψ hϖ d Ψ Y ∂matrixHaar K (t + 1) 1 = baseValue ϖ t d Ψ := by
  induction t generalizing d with
  | zero => exact integral_baseIntegrand_zero hϖ hψ d hΨ
  | succ t' ih => exact integral_baseIntegrand_succ hϖ hψ (fun d Ψ hΨ => ih d hΨ) d hΨ

end Langlands.Shahidi.OpenCell.Base
