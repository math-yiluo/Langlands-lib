import Langlands.Global.RankinSelberg.RealRectangularSmoothTransfer
import Langlands.Global.RankinSelberg.RealPairedDualConvergence

/-! # Ordinary tests in the span of reflected real rectangular integrals -/

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 1300000

namespace Langlands.Global.RankinSelbergGlobal.RealPairedRankRaising

open Langlands.Archimedean Langlands.Archimedean.DerivativeSmoothVectors
open Langlands.GeneralLinear (inverseTranspose weylLong weylInverseTranspose continuous_inverseTranspose)
open ArchimedeanLocal CompletedProjectiveRepresentation RealRectangularRows
open RealPairedSmoothRowAbsorption (slot unitProjection_slot_self unitProjection_slot_of_ne exists_productNorm_bound)
open RealPairedWhittakerGauge (coefficient contMDiff_slot slot_exp)
open RealPaddedWhittakerProduct (oppositeScale)
open ArchimedeanRealPairIdentity (sigmaFinite_measure)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure rectangularMeasure_zero_rows)
open RealUnequalLastRowDescent (colUnip colEntries)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable archimedeanRealQBorel

local notation "G" => fun m : ℕ => Langlands.GeneralLinear (m + 1) ℝ
local notation "N" => fun m : ℕ => Langlands.GeneralLinear.upperUnipotent (m + 1) ℝ
local notation "Q" => fun m : ℕ => LeftUnipotentQuotient m ℝ
local notation "Mat" => fun m : ℕ => Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ
local notation "Row" => fun t : ℕ => Fin (t + 1) → ℝ
local notation "Rect" => fun r t : ℕ => Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℝ
local notation "ι" => fun m : ℕ => inverseTranspose (m + 1) ℝ
local notation "wι" => fun m : ℕ => weylInverseTranspose (m + 1) ℝ
local notation "expU" => Langlands.LinearLieGroup.expUnit
local notation "height" => Langlands.Archimedean.unitHeight

variable (r t : ℕ)

local notation "n" => pairRanks r t
local notation "A" => fun i => Mat (n i)
local notation "B" => (∀ i : Fin 2, A i)
local notation "I" => 𝓘(ℝ, (∀ i : Fin 2, A i))

private def reflectedSlot : G r →* Bˣ := (slot n 0).comp (ι r).toMonoidHom

private def reflectedDirections (j : ℕ) : Row t →ₗ[ℝ] B :=
  -(ContinuousLinearMap.single ℝ A 0).toLinearMap.comp
    ((Matrix.transposeLinearEquiv _ _ ℝ ℝ).toLinearMap.comp (rowDirections r t j))

private theorem reflectedDirections_apply (j : ℕ) (y : Row t) :
    reflectedDirections r t j y = Pi.single 0 (-(rowDirections r t j y).transpose) := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp [reflectedDirections]
    rfl
  · change -(Pi.single (M := A) 0 ((rowDirections r t j y).transpose) i) = _
    rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi, neg_zero]

private theorem reflectedDirections_commute (j : ℕ) (y z : Row t) :
    Commute (reflectedDirections r t j y) (reflectedDirections r t j z) := by
  unfold Commute SemiconjBy
  simp only [reflectedDirections_apply]
  funext i
  by_cases hi : i = 0
  · subst i
    change Pi.single (M := A) 0 (-(rowDirections r t j y).transpose) 0 * Pi.single (M := A) 0 (-(rowDirections r t j z).transpose) 0 = _
    simp only [Pi.mul_apply, Pi.single_eq_same, neg_mul_neg, ← Matrix.transpose_mul,
      rowDirections_mul, Matrix.transpose_zero]
  · simp only [Pi.mul_apply, Pi.single_eq_of_ne hi, mul_zero]

private theorem reflectedDirections_exp (j : ℕ) (y : Row t) :
    expU B (reflectedDirections r t j y) = reflectedSlot r t (expU (Mat r) (rowDirections r t j y)) := by
  let X := rowDirections r t j y
  have hι : ι r (expU (Mat r) X) = matrixExpUnit (r + 1) (-X.transpose) := by
    apply Units.ext
    change (NormedSpace.exp (-X)).transpose = NormedSpace.exp (-X.transpose)
    rw [← Matrix.exp_transpose, Matrix.transpose_neg]
  rw [reflectedDirections_apply]
  change expU B (Pi.single (M := A) 0 (-X.transpose)) = slot n 0 (ι r (expU (Mat r) X))
  rw [hι]
  exact (by
    have hh := slot_exp n 0 (-X.transpose) 1
    simp only [one_smul] at hh
    exact hh.symm)

private def columnEntriesLinear (j : ℕ) : Row t →ₗ[ℝ] Mat r where
  toFun y := colEntries (extendColumn (j + 1) y)
  map_add' y z := by
    ext i l
    simp only [colEntries, extendColumn, Matrix.add_apply]
    split_ifs <;> simp only [Pi.add_apply, add_zero]
  map_smul' c y := by
    ext i l
    simp only [colEntries, extendColumn, Matrix.smul_apply]
    split_ifs <;> simp only [Pi.smul_apply, RingHom.id_apply, smul_zero]

private theorem reflectedColumn_height (j : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : Row t, height (reflectedSlot r t (colUnip (extendColumn (j + 1) y))) ≤
      K * max 1 ‖y‖ := by
  let C := (ContinuousLinearMap.single ℝ A 0).comp
    (((Matrix.transposeLinearEquiv _ _ ℝ ℝ).toLinearMap.comp (columnEntriesLinear r t j)).toContinuousLinearMap)
  let K := 1 + ‖(1 : B)‖ + ‖C‖
  have hK : 1 ≤ K := by dsimp [K]; linarith only [norm_nonneg (1 : B), norm_nonneg C]
  refine ⟨K, zero_le_one.trans hK, fun y => ?_⟩
  let g := reflectedSlot r t (colUnip (extendColumn (j + 1) y))
  have hSlot : g = slot n 0 (ι r (colUnip (extendColumn (j + 1) y))) := rfl
  have hG : g.val = 1 - C y ∧ (g⁻¹ : Bˣ).val = 1 + C y := by
    constructor <;> funext i
    · change (unitProjection A i g).val = _
      by_cases hi : i = 0
      · subst i
        rw [hSlot, unitProjection_slot_self]
        change Matrix.transpose ((1 : Mat r) - colEntries (extendColumn (j + 1) y)) = _
        simp only [Matrix.transpose_sub, Matrix.transpose_one, Pi.sub_apply, Pi.one_apply, C,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply, Pi.single_eq_same]
        rfl
      · rw [hSlot, unitProjection_slot_of_ne n hi]
        simp only [Units.val_one, Pi.sub_apply, Pi.one_apply, C, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.single_apply, Pi.single_eq_of_ne hi, sub_zero]
    · change (unitProjection A i (g⁻¹ : Bˣ)).val = _
      rw [map_inv]
      by_cases hi : i = 0
      · subst i
        rw [hSlot, unitProjection_slot_self]
        change Matrix.transpose ((1 : Mat r) + colEntries (extendColumn (j + 1) y)) = _
        simp only [Matrix.transpose_add, Matrix.transpose_one, Pi.add_apply, Pi.one_apply, C,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply, Pi.single_eq_same]
        rfl
      · rw [hSlot, unitProjection_slot_of_ne n hi]
        simp only [inv_one, Units.val_one, Pi.add_apply, Pi.one_apply, C, ContinuousLinearMap.comp_apply,
          ContinuousLinearMap.single_apply, Pi.single_eq_of_ne hi, add_zero]
  change height g ≤ _
  have hb : ‖(1 : B)‖ + ‖C y‖ ≤ K * max 1 ‖y‖ := calc
    _ ≤ ‖(1 : B)‖ * max 1 ‖y‖ + ‖C‖ * max 1 ‖y‖ :=
      add_le_add (le_mul_of_one_le_right (norm_nonneg _) (le_max_left _ _))
        ((C.le_opNorm y).trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg C)))
    _ ≤ _ := by rw [← add_mul]; gcongr; dsimp [K]; linarith
  unfold Langlands.Archimedean.unitHeight
  rw [hG.1, hG.2]
  exact max_le (one_le_mul_of_one_le_of_one_le hK (le_max_left _ _))
    (max_le ((norm_sub_le _ _).trans hb) ((norm_add_le _ _).trans hb))

variable (E : Fin 2 → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
  (R : ∀ i, G (pairRanks r t i) →* (E i →L[ℂ] E i))

local notation "P" => productAction A R
local notation "D" => DerivativeSmoothVectors I P
local notation "act" => DerivativeSmoothVectors.representation I P

private local instance : ChartedSpace B Bˣ :=
  (Units.isOpenEmbedding_val (R := B)).singletonChartedSpace

/-- The ordinary kernel on the two Weyl inverse-transpose coefficients. -/
def reflectedOrdinaryKernel (h : t < r) (T : D →L[ℂ] ℂ) (v : D) (s : ℂ) (q : Q t) : ℂ :=
  let g : G t := q.out
  let p : G r := padGL (Nat.succ_le_succ h.le) g
  reflectedPairCoefficient r t E R (1 : G r) T v p g *
    ArchimedeanLocal.detPower realNormalizedAbs g (s - ((r - t : ℕ) : ℂ) / 2)

private def reflectedBase (T : D →L[ℂ] ℂ) (q : Q t) : D →L[ℂ] ℂ :=
  let u : Bˣ := slot n 1 (wι t q.out) * slot n 0 (weylLong (r + 1) ℝ)
  T.comp (SmoothAction.derivativeAction I P u)

private theorem reflectedBase_eq (T : D →L[ℂ] ℂ) (q : Q t) (g : G r) (v : D) :
    reflectedBase r t E R T q (act (reflectedSlot r t g) v) =
      reflectedPairCoefficient r t E R (1 : G r) T v g q.out := by
  unfold reflectedBase reflectedSlot reflectedPairCoefficient coefficient
  change T (act (slot n 1 (wι t q.out) * slot n 0 (weylLong (r + 1) ℝ))
      (act (slot n 0 (ι r g)) v)) = _
  rw [← Module.End.mul_apply, ← map_mul, mul_assoc, ← map_mul, mul_one]
  rfl

private theorem reflectedPairCoefficient_remove_right (w : G r) (T : D →L[ℂ] ℂ)
    (v : D) (g : G r) (g' : G t) :
    reflectedPairCoefficient r t E R w T (act (slot n 0 ((ι r w)⁻¹)) v) g g' =
      reflectedPairCoefficient r t E R (1 : G r) T v g g' := by
  unfold reflectedPairCoefficient coefficient
  change T (act (slot n 1 (wι t g') * slot n 0 (wι r (g * w)))
    (act (slot n 0 ((ι r w)⁻¹)) v)) = _
  rw [← Module.End.mul_apply, ← map_mul, mul_assoc, ← map_mul, mul_one]
  have he : wι r (g * w) * (ι r w)⁻¹ = wι r g := by
    change (weylLong (r + 1) ℝ * ι r (g * w)) * (ι r w)⁻¹ = weylLong (r + 1) ℝ * ι r g
    rw [map_mul, mul_assoc, mul_inv_cancel_right]
  rw [he]

variable [∀ i, CompleteSpace (E i)]

/-- Each reflected ordinary integral is a finite sum of the actual reflected rectangular
integrals with the same spectral parameter and prescribed compatible quotient measure. -/
def RealPairedReflectedOrdinaryTransferStatement : Prop :=
  (∀ i, IsContinuousRepresentation (R i)) →
    ∀ (h : t < r) (a : ℝˣ) (μ : RealQuotientMeasureData t) (T : D →L[ℂ] ℂ),
      (∀ (i : Fin 2) (u : N (n i)) (v : D), T (act (slot n i u.val) v) =
        realWhittakerCharacter (oppositeScale a i) u.val * T v) →
      ∃ σ : ℝ, ∀ v : D, ∃ (k : ℕ) (u : Fin k → D), ∀ s : ℂ, σ < s.re →
        Integrable (reflectedOrdinaryKernel r t E R h T v s) μ.measure ∧
        (∫ q, reflectedOrdinaryKernel r t E R h T v s q ∂μ.measure) =
          ∑ i, ∫ p, unequalPairedDualKernel r t E R h T (u i) s p ∂(realUnequalDualMeasure (r := r) a μ)

set_option maxHeartbeats 1400000 in
theorem realPairedReflectedOrdinaryTransfer : RealPairedReflectedOrdinaryTransferStatement r t E R := by
  intro hR h a μ T hCov
  let ν := realSelfDualMeasure a
  have : ν.measure.IsAddHaarMeasure := ν.isAddHaar
  have : SigmaFinite ν.measure := inferInstance
  have : SigmaFinite μ.measure := sigmaFinite_measure μ
  let k := r - (t + 1)
  let L := reflectedBase r t E R T
  let wt (s : ℂ) (q : Q t) := ArchimedeanLocal.detPower realNormalizedAbs q.out (s - ((r - t : ℕ) : ℂ) / 2)
  let K := prefixKernel P h (reflectedSlot r t) L wt
  have hKernel (j : ℕ) (v : D) (s : ℂ) (p : Q t × Matrix (Fin j) (Fin (t + 1)) ℝ) :
      K j v s p = reflectedPairCoefficient r t E R (1 : G r) T v (point h p.1.out p.2) p.1.out * wt s p.1 := by
    unfold K prefixKernel
    rw [reflectedBase_eq]
  have hL (q : Q t) (u : N r) (v : D) : L q (act (reflectedSlot r t u.val) v) =
      realWhittakerCharacter (-a) u.val * L q v := by
    rw [reflectedBase_eq]
    have hh := (reflectedPairCoefficient_mul r t E R (1 : G r) T a hCov v).1 u 1 q.out
    rw [mul_one] at hh
    rw [hh]
    have he := reflectedBase_eq r t E R T q 1 v
    rw [map_one, map_one, Module.End.one_apply] at he
    rw [← he]
  have hρ : Continuous (reflectedSlot r t) :=
    (contMDiff_slot n 0).continuous.comp (continuous_inverseTranspose _ _)
  have hStep := realRectangularSmoothTransfer P h (reflectedSlot r t) (isContinuous_productAction A R hR)
    hρ (-a) μ ν L wt hL (fun j _ => ⟨reflectedDirections r t j, reflectedDirections_commute r t j,
      reflectedDirections_exp r t j⟩) (fun j _ => reflectedColumn_height r t j)
    (exists_productNorm_bound n E R hR) 0 (Nat.zero_le k)
  obtain ⟨σ, hI⟩ := realPairedUnequalDualConvergence r t E R hR h a T hCov μ
  refine ⟨σ, fun v => ?_⟩
  obtain ⟨l, z, hz⟩ := hStep v
  let u (i : Fin l) := act (slot n 0 ((ι r (ArchimedeanLocal.unfoldingWeyl h))⁻¹)) (z i)
  refine ⟨l, u, fun s hs => ?_⟩
  have hTop (i : Fin l) : K k (z i) s = unequalPairedDualKernel r t E R h T (u i) s := by
    funext p
    rw [hKernel, point_full]
    unfold unequalPairedDualKernel unequalDualPairCoefficient u
    rw [reflectedPairCoefficient_remove_right]
  have hI' (i : Fin l) : Integrable (K k (z i) s) (μ.measure.prod (rectangularMeasure ν k (t + 1))) :=
    hTop i ▸ (hI (u i)).1 s hs
  have hEq₀ : K 0 v s = fun p => reflectedOrdinaryKernel r t E R h T v s p.1 := by
    funext p
    rw [hKernel, point_zero]
    rfl
  obtain ⟨hi, he⟩ := hz s hI'
  change Integrable (K 0 v s) (μ.measure.prod (rectangularMeasure ν 0 (t + 1))) at hi
  change (∫ p, K 0 v s p ∂(μ.measure.prod (rectangularMeasure ν 0 (t + 1)))) =
    ∑ i, ∫ p, K k (z i) s p ∂(μ.measure.prod (rectangularMeasure ν k (t + 1))) at he
  rw [hEq₀, rectangularMeasure_zero_rows] at hi he
  have hn : Measure.dirac (0 : Matrix (Fin 0) (Fin (t + 1)) ℝ) ≠ 0 := Measure.dirac_ne_zero
  have hi₀ := (Integrable.comp_fst_iff hn).1 hi
  refine ⟨hi₀, ?_⟩
  rw [integral_prod _ hi] at he
  simpa only [integral_dirac, hTop, realUnequalDualMeasure] using he

end Langlands.Global.RankinSelbergGlobal.RealPairedRankRaising
