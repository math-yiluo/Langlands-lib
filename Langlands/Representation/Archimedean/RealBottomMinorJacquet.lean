import Langlands.Representation.Archimedean.RealBottomMinorTriangular
import Langlands.Representation.Archimedean.RealCharacterCrossing
import Langlands.Representation.Archimedean.RealSubquotientEval

/-! # Jacquet functionals from products of real bottom minors -/

noncomputable section

open Finset Matrix
open scoped TensorProduct Matrix.Norms.Operator

namespace Langlands.Archimedean.RealBottomMinorJacquet

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open RealBottomMinorProducts RealBottomMinorTriangular RealTemperedCommutantReduction
open RealTiedMinorScalar RealTiedMinorProduct
open RealCharacterCrossing (PL PL_position_neg_one chars_list_eq)
open RealJacquetFrobenius (chars expo posChar)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n q : ℕ} {degree : Fin q → ℕ} {ds es fs : List RealBlock}

/-- The exponent in the left covariance law, including the Borel modulus. -/
def jacquetExponent (τ : Fin n → ℂ) (i : Fin n) : ℂ :=
  τ i + (((n : ℂ) - 1) / 2 - (i.val : ℂ))

private theorem expo_jacquetExponent (τ : Fin n → ℂ) : expo (jacquetExponent τ) = τ := by
  funext i
  dsimp [expo, jacquetExponent]
  ring

/-- Evaluation at the identity has the Jacquet parameters of the target
principal series. -/
theorem isJacquet_eval (τ : Fin n → ℂ) (e : Fin n → Fin 2) :
    IsRealJacquetFunctional n (realStandardRep n (PL τ e)) (realStandardLie n (PL τ e))
      (kFiniteEval (realStandardModule n (PL τ e)) 1) (jacquetExponent τ) e := by
  have hpos : posChar (jacquetExponent τ) e = realPositionCharacter (PL τ e) := by
    change realPositionCharacter ((List.ofFn (chars (jacquetExponent τ) e)).map RealBlock.character) = _
    rw [chars_list_eq, expo_jacquetExponent]
  have hUpper (f : KF n (PL τ e)) (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.IsUpperTriangular) :
      kFiniteEval (realStandardModule n (PL τ e)) 1 (realStandardLie n (PL τ e) (1 ⊗ₜ X) f) =
        (∑ j, jacquetExponent τ j * (X j j : ℂ)) * f.val 1 := by
    have hf : f.val ∈ principalSeries ℝ n (posChar (jacquetExponent τ) e) := by
      rw [hpos]
      exact realStandardModule_le_principalSeries n (PL τ e) f.2.1
    simpa only [kFiniteEval_apply, realStandardLie_one_tmul_apply_coe] using
      RealSubquotient.rightDerivative_upper_apply_one hf hX
  constructor
  · intro X hX f
    rw [hUpper f X (fun {i j} hij => hX i j hij.le)]
    simp only [hX _ _ le_rfl, Complex.ofReal_zero, mul_zero, sum_const_zero, zero_mul]
  · intro i f
    constructor
    · have hX : (Matrix.single i i (1 : ℝ)).IsUpperTriangular := by
        intro j k hjk
        simp only [Matrix.single_apply]
        split_ifs with h
        · obtain ⟨rfl, rfl⟩ := h
          exact (lt_irrefl _ hjk).elim
        · rfl
      rw [hUpper f _ hX, sum_eq_single i]
      · simp [kFiniteEval_apply]
      · intro j _ hj
        simp [Ne.symm hj]
      · simp
    · change f.val (1 * Unitary.toUnits (signReflection n i)) =
        (-1) ^ (e i).val * f.val 1
      have hs := RealBlockFourierFinite.apply_signReflection_mul
        (RealStrictCharacterLanglandsQuotient.isSignedPower (PL τ e)).one
        (realStandardModule_le_principalSeries n (PL τ e) f.2.1) i 1
      simpa only [one_mul, mul_one, PL_position_neg_one] using hs

variable (hds : IsPrincipal ds) (hes : IsPrincipal es) (R : Selection n degree)
  (hBottom : ∀ t, IsBottom (R t).val)
  (hShift : ∀ a : Fin n → ℝˣ,
    principalSeriesCharacter ℝ n (realPositionCharacter ds) a =
      principalSeriesCharacter ℝ n (realPositionCharacter es) a * diagonalFactor R a)

local notation "M" => fun C => multiply hds hes R C hBottom hShift

/-- Multiply by the specified bottom-minor coefficient, apply the linear
map, and evaluate the resulting function at the identity. -/
def coefficientFunctional (U : KF n ds →ₗ[ℂ] KF n fs) (C : Selection n degree) :
    KF n es →ₗ[ℂ] ℂ :=
  (kFiniteEval (realStandardModule n fs) 1).comp (U.comp (M C))

variable {hds hes R hBottom hShift}

local notation "F" => fun U C => coefficientFunctional hds hes R hBottom hShift U C

/-- A nonzero compact intertwiner has a nonzero coefficient functional.
The products jointly span the source of the intertwiner, and compact
translates separate its outputs by evaluation at the identity. -/
theorem exists_ne_zero (U : KF n ds →ₗ[ℂ] KF n fs) (hU : U ≠ 0)
    (hUK : ∀ k v, U (realStandardRep n ds k v) = realStandardRep n fs k (U v)) :
    ∃ C : Selection n degree, F U C ≠ 0 := by
  by_contra! h
  have hEval (v : KF n ds) : kFiniteEval (realStandardModule n fs) 1 (U v) = 0 := by
    have hv : ∃ a : Selection n degree → KF n es, (∑ C, M C (a C)) = v :=
      ⟨_, sum_multiply_extract hds hes R hBottom hShift v⟩
    obtain ⟨a, ha⟩ := hv
    rw [← ha, map_sum, map_sum]
    exact Finset.sum_eq_zero fun C _ => by
      have hC := DFunLike.congr_fun (h C) (a C)
      exact hC
  apply hU
  apply LinearMap.ext
  intro v
  apply eq_zero_of_compact_eval n fs
  intro k
  rw [← hUK]
  exact hEval _

private theorem rep_multiply_signReflection (C : Selection n degree) (j : Fin n) (v : KF n es) :
    realStandardRep n ds (signReflection n j) (M C v) =
      (-1 : ℂ) ^ columnWeight C j • M C (realStandardRep n es (signReflection n j) v) := by
  apply Subtype.ext
  funext g
  change v.val (g * Unitary.toUnits (signReflection n j)) *
      coefficient R C (g * Unitary.toUnits (signReflection n j)) =
    (-1 : ℂ) ^ columnWeight C j *
      (v.val (g * Unitary.toUnits (signReflection n j)) * coefficient R C g)
  rw [coefficient_mul]
  simp only [coefficient_signReflection, mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]
  ring

private theorem neg_one_pow_mod_two (m : ℕ) : (-1 : ℂ) ^ m = (-1) ^ (m % 2) := by
  conv_lhs => rw [← Nat.div_add_mod m 2, pow_add, pow_mul]
  norm_num

/-- The character on a sign reflection after dividing by the column
configuration's diagonal character. -/
def shiftedParity (e : Fin n → Fin 2) (C : Selection n degree) (i : Fin n) : Fin 2 :=
  ⟨((e i).val + columnWeight C i) % 2, Nat.mod_lt _ (by decide)⟩

/-- If all coefficient functionals with smaller index sum vanish, the
remaining functional has the Jacquet parameters of the target with the
column weight subtracted. -/
theorem isJacquet_of_lower_zero {τ : Fin n → ℂ} {e : Fin n → Fin 2}
    (U : KF n ds →ₗ[ℂ] KF n (PL τ e))
    (hUK : ∀ k v, U (realStandardRep n ds k v) = realStandardRep n (PL τ e) k (U v))
    (hUL : ∀ (X : Matrix (Fin n) (Fin n) ℝ) v,
      U (realStandardLie n ds (1 ⊗ₜ X) v) = realStandardLie n (PL τ e) (1 ⊗ₜ X) (U v))
    (C : Selection n degree)
    (hC : ∀ B, indexSum B < indexSum C → F U B = 0) :
    IsRealJacquetFunctional n (realStandardRep n es) (realStandardLie n es) (F U C)
      (fun j => jacquetExponent τ j - (columnWeight C j : ℂ)) (shiftedParity e C) := by
  let ev := kFiniteEval (realStandardModule n (PL τ e)) 1
  have hEval := isJacquet_eval τ e
  have hLie (X : Matrix (Fin n) (Fin n) ℝ) (v : KF n es) :
      F U C (realStandardLie n es (1 ⊗ₜ X) v) =
        ev (realStandardLie n (PL τ e) (1 ⊗ₜ X) (U (M C v))) -
          ∑ B : Selection n degree,
            rightDerivative (matrixModel ℝ n) X (coefficient B C) 1 * F U B v := by
    change ev (U (M C (realStandardLie n es (1 ⊗ₜ X) v))) = _
    rw [multiply_lie, map_sub, hUL, map_sub, map_sum, map_sum]
    simp only [map_smul, smul_eq_mul, coefficientFunctional, LinearMap.comp_apply, ev]
  constructor
  · intro X hX v
    rw [hLie, hEval.1 X hX]
    suffices h : (∑ B : Selection n degree,
        rightDerivative (matrixModel ℝ n) X (coefficient B C) 1 * F U B v) = 0 by
      rw [h, sub_zero]
    apply Finset.sum_eq_zero
    intro B _
    by_cases hB : indexSum B < indexSum C
    · simp only [hC B hB, LinearMap.zero_apply, mul_zero]
    · rw [rightDerivative_coefficient_strictUpper_zero B C X hX (not_lt.mp hB), zero_mul]
  · intro j v
    constructor
    · rw [hLie, (hEval.2 j (U (M C v))).1]
      simp only [rightDerivative_coefficient_diagonal, ite_mul, zero_mul, sum_ite_eq',
        mem_univ, ite_true, sub_mul]
      rfl
    · let s := (-1 : ℂ) ^ columnWeight C j
      have hs : s * s = 1 := by
        simp only [s, ← mul_pow, neg_mul_neg, one_mul, one_pow]
      have hsign : s * F U C (realStandardRep n es (signReflection n j) v) =
          (-1) ^ (e j).val * F U C v := by
        have h := (hEval.2 j (U (M C v))).2
        rw [← hUK, rep_multiply_signReflection C j v, map_smul, map_smul, smul_eq_mul] at h
        exact h
      calc
        _ = s * (s * F U C (realStandardRep n es (signReflection n j) v)) := by
          rw [← mul_assoc, hs, one_mul]
        _ = (-1) ^ (shiftedParity e C j).val * F U C v := by
          rw [hsign, ← mul_assoc]
          congr 1
          rw [mul_comm, shiftedParity, ← neg_one_pow_mod_two ((e j).val + columnWeight C j), pow_add]

/-- A nonzero compact and Lie intertwiner into the target principal series
gives a nonzero Jacquet functional from a column configuration with minimal
index sum among the nonzero coefficient functionals. -/
theorem exists_minimal_isJacquet {τ : Fin n → ℂ} {e : Fin n → Fin 2}
    (U : KF n ds →ₗ[ℂ] KF n (PL τ e)) (hU : U ≠ 0)
    (hUK : ∀ k v, U (realStandardRep n ds k v) = realStandardRep n (PL τ e) k (U v))
    (hUL : ∀ (X : Matrix (Fin n) (Fin n) ℝ) v,
      U (realStandardLie n ds (1 ⊗ₜ X) v) = realStandardLie n (PL τ e) (1 ⊗ₜ X) (U v)) :
    ∃ C : Selection n degree, F U C ≠ 0 ∧
      (∀ B, indexSum B < indexSum C → F U B = 0) ∧
      IsRealJacquetFunctional n (realStandardRep n es) (realStandardLie n es) (F U C)
        (fun j => jacquetExponent τ j - (columnWeight C j : ℂ)) (shiftedParity e C) := by
  classical
  obtain ⟨C, hC⟩ := exists_ne_zero (R := R) (hBottom := hBottom) (hShift := hShift) U hU hUK
  have hex : ∃ m : ℕ, ∃ B : Selection n degree, indexSum B = m ∧ F U B ≠ 0 :=
    ⟨indexSum C, C, rfl, hC⟩
  obtain ⟨B, hB, hBne⟩ := Nat.find_spec hex
  have hmin (D : Selection n degree) (hD : indexSum D < indexSum B) : F U D = 0 := by
    by_contra hDne
    have hle := Nat.find_min' hex ⟨D, rfl, hDne⟩
    omega
  exact ⟨B, hBne, hmin, isJacquet_of_lower_zero U hUK hUL B hmin⟩

end Langlands.Archimedean.RealBottomMinorJacquet
