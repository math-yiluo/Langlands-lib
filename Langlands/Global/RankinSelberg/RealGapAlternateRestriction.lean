import Langlands.Global.RankinSelberg.RealGapTailExchange
import Langlands.Global.RankinSelberg.RealGapTriangularChart
import Langlands.Global.RankinSelberg.RealGodementPaddedRestriction

/-! # The alternate split real Godement integral in the larger rank difference -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapAlternateRestriction

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (rankInclusion determinant blockSum_apply_right blockSum_apply_right_left)
open Langlands.LocalFactor.Archimedean (RealBlock RealCharacterData realScaledCharacter)
open Langlands.RankinSelberg (rectangularMeasure lastRow_mul_eq_vecMul det_rankInclusion)
open ArchimedeanLocal (realNormalizedAbs realSelfDualMeasure realFourierTransform RealQuotientMeasureData)
open RealJacquet (realAdjacentGodementCoefficient realAdjacentWeylSign detCharacter joinLastColumn)
open RealGapTailExchange
open RealGapTriangularChart (Outer outerMeasure retainedMatrix triangularRightChart
  continuous_triangularRightChart diagonalWeightMeasure)
open RealGapUpperTail (packedTail laterRectangle)
open RealGodementPaddedRestriction (paddedRestrictionKernel realGodementPaddedRestriction)
open RealJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)

local instance gapGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
local instance gapGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
local instance gapNMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := borel _
local instance gapNBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
local instance gapQMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.RankinSelberg.LeftUnipotentQuotient n ℝ) := borel _
local instance gapMatrixSecondCountable (m n : ℕ) :
    SecondCountableTopology (Matrix (Fin m) (Fin n) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
local instance gapGLSecondCountable (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear n ℝ) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) n).isInducing.secondCountableTopology

variable (k q : ℕ)

local notation "I" => Fin (k + q + 1)
local notation "J" => Fin (q + 1)
local notation "Vec" => I → ℝ
local notation "G" => Langlands.GeneralLinear (k + q + 1) ℝ
local notation "H" => Langlands.GeneralLinear k ℝ
local notation "Compact" => unitaryCompact ℝ (k + q + 1)
local notation "N" => Langlands.GeneralLinear.upperUnipotent (q + 1) ℝ
local notation "Remainder" => Matrix (Fin k) (Fin q) ℝ × N
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs

/-- A split test has a leading rectangular factor, one factor for each column of the square
block after the leading ones, and a factor for the free last column. -/
structure GodementColumnFactors where
  leading : 𝓢(Matrix I (Fin k) ℝ, ℂ)
  tail : Fin (q + 2) → 𝓢(Vec, ℂ)

/-- The square part of the split test: the leading rectangle and the tail columns. -/
def GodementColumnFactors.squareEval (T : GodementColumnFactors k q) (A : Matrix I I ℝ) : ℂ :=
  T.leading (fun i j => A i (j.castAdd (q + 1))) *
    ∏ j : J, T.tail j.castSucc (fun i => A i (j.natAdd k))

/-- The full rectangular evaluation of split factors: the leading rectangle and all tail
columns, including the free last column. -/
def GodementColumnFactors.eval (T : GodementColumnFactors k q) (X : Matrix I (Fin (k + q + 2)) ℝ) : ℂ :=
  T.leading (fun i j => X i (j.castAdd (q + 2))) *
    ∏ j : Fin (q + 2), T.tail j (fun i => X i (j.natAdd k))

/-- On a joined rectangle the full evaluation is the square evaluation times the last factor. -/
theorem GodementColumnFactors.eval_joinLastColumn (T : GodementColumnFactors k q)
    (A : Matrix I I ℝ) (x : I → ℝ) :
    T.eval k q (joinLastColumn A x) = T.squareEval k q A * T.tail (Fin.last (q + 1)) x := by
  unfold GodementColumnFactors.eval GodementColumnFactors.squareEval
  rw [Fin.prod_univ_castSucc, ← mul_assoc]
  have hLead : (fun (i : I) (j : Fin k) => joinLastColumn A x i (j.castAdd (q + 2))) =
      fun i j => A i (j.castAdd (q + 1)) := by
    funext i j
    change Fin.lastCases (motive := fun _ => ℝ) (x i) (A i) ((j.castAdd (q + 1)).castSucc) = _
    rw [Fin.lastCases_castSucc]
  have hTail (j : Fin (q + 1)) : (fun i : I => joinLastColumn A x i (j.castSucc.natAdd k)) =
      fun i => A i (j.natAdd k) := by
    funext i
    change Fin.lastCases (motive := fun _ => ℝ) (x i) (A i) ((j.natAdd k).castSucc) = _
    rw [Fin.lastCases_castSucc]
  have hLast : (fun i : I => joinLastColumn A x i ((Fin.last (q + 1)).natAdd k)) = x := by
    funext i
    change Fin.lastCases (motive := fun _ => ℝ) (x i) (A i) (Fin.last (k + q + 1)) = _
    rw [Fin.lastCases_last]
  simp only [hLead, hTail, hLast]

/-- Every rectangle is the join of its leading square and its last column. -/
theorem joinLastColumn_split (X : Matrix I (Fin (k + q + 2)) ℝ) :
    joinLastColumn (fun i (j : I) => X i j.castSucc) (fun i => X i (Fin.last (k + q + 1))) = X := by
  ext i j
  induction j using Fin.lastCases with
  | last =>
    change Fin.lastCases (motive := fun _ => ℝ) _ _ (Fin.last (k + q + 1)) = _
    rw [Fin.lastCases_last]
  | cast j =>
    change Fin.lastCases (motive := fun _ => ℝ) _ _ j.castSucc = _
    rw [Fin.lastCases_castSucc]

/-- The factors entering the restricted kernel, with the free column Fourier transformed. -/
def GodementColumnFactors.partial (T : GodementColumnFactors k q) (a : ℝˣ) : SplitTailTest k q where
  leading := T.leading
  first := T.tail 0
  later j := T.tail j.succ.castSucc
  lastFrequency := realFourierTransform a (T.tail (Fin.last (q + 1)))

private theorem squareEval_split (T : GodementColumnFactors k q) (A : Matrix I I ℝ) :
    T.squareEval k q A =
      T.leading (fun i j => A i (j.castAdd (q + 1))) * T.tail 0 (fun i => A i ((0 : J).natAdd k)) *
        ∏ j : Fin q, T.tail j.succ.castSucc (fun i => A i (j.succ.natAdd k)) := by
  unfold GodementColumnFactors.squareEval
  rw [Fin.prod_univ_succ, Fin.castSucc_zero, mul_assoc]

private theorem lastRow_rankInclusion (h : H) :
    Langlands.RankinSelberg.lastRow (rankInclusion (q + 1) h) = Langlands.RankinSelberg.lastRow (1 : G) := by
  have hl : (Fin.last q).natAdd k = Fin.last (k + q) := Fin.ext rfl
  funext j
  change (rankInclusion (q + 1) h).val (Fin.last (k + q)) j = (1 : Matrix I I ℝ) (Fin.last (k + q)) j
  rw [← hl]
  refine Fin.addCases (m := k) (n := q + 1) (fun j₀ => ?_) (fun j₁ => ?_) j
  · rw [show (rankInclusion (q + 1) h).val ((Fin.last q).natAdd k) (j₀.castAdd (q + 1)) = 0 from
      blockSum_apply_right_left h 1 (Fin.last q) j₀]
    rw [Matrix.one_apply_ne]
    intro he
    have he' := congrArg Fin.val he
    change k + q = j₀.val at he'
    omega
  · rw [show (rankInclusion (q + 1) h).val ((Fin.last q).natAdd k) (j₁.natAdd k) =
      (1 : Matrix J J ℝ) (Fin.last q) j₁ from blockSum_apply_right h 1 (Fin.last q) j₁,
      Matrix.one_apply, Matrix.one_apply]
    congr 1
    exact propext ⟨fun e => congrArg (Fin.natAdd k) e, fun e => Fin.ext (by simpa using congrArg Fin.val e)⟩

private theorem tailColumn_rankInclusion (C : G) (h : H) (j : J) :
    (fun i : I => (C * rankInclusion (q + 1) h).val i (j.natAdd k)) = fun i => C.val i (j.natAdd k) := by
  have hc : (fun i : I => (rankInclusion (q + 1) h).val i (j.natAdd k)) =
      fun i => (1 : Matrix I I ℝ) i (j.natAdd k) := by
    funext i
    refine Fin.addCases (m := k) (n := q + 1) (fun i₀ => ?_) (fun i₁ => ?_) i
    · rw [show (rankInclusion (q + 1) h).val (i₀.castAdd (q + 1)) (j.natAdd k) = 0 from
        Langlands.GeneralLinear.blockSum_apply_left_right h 1 i₀ j, Matrix.one_apply_ne]
      intro e
      have he := congrArg Fin.val e
      change i₀.val = k + j.val at he
      omega
    · rw [show (rankInclusion (q + 1) h).val (i₁.natAdd k) (j.natAdd k) = (1 : Matrix J J ℝ) i₁ j from
          blockSum_apply_right h 1 i₁ j,
        Matrix.one_apply, Matrix.one_apply]
      congr 1
      exact propext ⟨fun e => congrArg (Fin.natAdd k) e, fun e => Fin.ext (by simpa using congrArg Fin.val e)⟩
  change C.val.mulVec (fun i => (rankInclusion (q + 1) h).val i (j.natAdd k)) = _
  rw [hc]
  change (fun i => (C.val * (1 : Matrix I I ℝ)) i (j.natAdd k)) = _
  rw [Matrix.mul_one]

/-- The adjoining character and determinant power `η(x) |x|^{(k+q)/2}` of the changed
Godement variable, as a multiplicative function. -/
def restrictionWeight (c : RealCharacterData) : ℝˣ →* ℂ where
  toFun x := (c.character.toMonoidHom x : ℂ) *
    Complex.exp ((((k + q : ℕ) : ℂ)) / 2 * (Real.log |(x : ℝ)| : ℂ))
  map_one' := by simp
  map_mul' x y := by
    have hx : |(x : ℝ)| ≠ 0 := abs_ne_zero.mpr x.ne_zero
    have hy : |(y : ℝ)| ≠ 0 := abs_ne_zero.mpr y.ne_zero
    simp only [map_mul, Units.val_mul, abs_mul, Real.log_mul hx hy, Complex.ofReal_add, mul_add,
      Complex.exp_add]
    ring

private theorem restrictionWeight_det (c : RealCharacterData) {n : ℕ}
    (g : Langlands.GeneralLinear n ℝ) :
    restrictionWeight k q c (determinant g) =
      detCharacter c.character.toMonoidHom g * P g (((k + q : ℕ) : ℂ) / 2) := by
  rfl

/-- Pointwise identification on a chart with any retained matrix. -/
theorem paddedRestrictionKernel_split (a : ℝˣ) (c : RealCharacterData)
    (T : GodementColumnFactors k q) (F : Matrix I I ℝ → ℂ) (hF : ∀ A, F A = T.squareEval k q A)
    (U : G → ℂ) (g h : H) (B : G) (p : Remainder) :
    paddedRestrictionKernel c a F (T.tail (Fin.last (q + 1))) U (rankInclusion (q + 1) g) 1
        (B * (packedTail k q (laterRectangle k q p.1) p.2).val * rankInclusion (q + 1) h) =
      ordinaryBlockTailKernel k q (T.partial k q a) U (restrictionWeight k q c) g h B p := by
  let C := B * (packedTail k q (laterRectangle k q p.1) p.2).val
  let A : G := rankInclusion (q + 1) h
  let g₀ : G := rankInclusion (q + 1) g
  let χ := restrictionWeight k q c
  have hW : g₀ * (C * A)⁻¹ = rankInclusion (q + 1) (g * h⁻¹) * C⁻¹ := by
    simp only [A, g₀, mul_inv_rev, map_mul, map_inv, mul_assoc]
  have hRow : Langlands.RankinSelberg.lastRow (g₀ * (C * A)⁻¹) = Langlands.RankinSelberg.lastRow C⁻¹ := by
    rw [hW, lastRow_mul_eq_vecMul, lastRow_rankInclusion k q, ← lastRow_mul_eq_vecMul, one_mul]
  have hdet : determinant A = determinant h := Units.ext (det_rankInclusion (q + 1) h)
  have hWeight : χ (determinant (C * A)) = χ (determinant C) * χ (determinant h) := by
    rw [map_mul determinant, map_mul χ]
    exact congrArg (fun z => χ (determinant C) * χ z) hdet
  have hK : detCharacter c.character.toMonoidHom (C * A) * P (C * A) (((k + q : ℕ) : ℂ) / 2) =
      χ (determinant (C * A)) := (restrictionWeight_det k q c (C * A)).symm
  unfold paddedRestrictionKernel
  change F (C * A * 1).val * realFourierTransform a (T.tail (Fin.last (q + 1)))
      (Langlands.RankinSelberg.lastRow (g₀ * (C * A)⁻¹)) * U (g₀ * (C * A)⁻¹) *
      detCharacter c.character.toMonoidHom (C * A) * P (C * A) (((k + q : ℕ) : ℂ) / 2) = _
  rw [mul_one, hRow, hW, mul_assoc _ (detCharacter _ _), hK, hWeight, hF, squareEval_split]
  simp only [A, tailColumn_rankInclusion]
  unfold ordinaryBlockTailKernel fixedTailFactor GodementColumnFactors.partial
  change _ = (T.leading (fun i j => (C * A).val i (j.castAdd (q + 1))) *
    T.tail 0 (fun i => C.val i ((0 : J).natAdd k)) *
    realFourierTransform a (T.tail (Fin.last (q + 1))) (Langlands.RankinSelberg.lastRow C⁻¹) *
    U (rankInclusion (q + 1) (g * h⁻¹) * C⁻¹) * χ (determinant h) * χ (determinant C)) *
    ∏ j : Fin q, T.tail j.succ.castSucc (fun i => C.val i (j.succ.natAdd k))
  ring

/-- The alternate kernel after Fourier transformation in the later columns, with its Jacobian. -/
def alternateRestrictionKernel (a : ℝˣ) (c : RealCharacterData) (T : GodementColumnFactors k q)
    (U : G → ℂ) (g : H) (p : Outer k q) (Z : N) : ℂ :=
  let B := retainedMatrix k q p
  (((realNormalizedAbs B.val.det)⁻¹ : ℝ) : ℂ) ^ q *
    alternateBlockTailKernel k q a (T.partial k q a) U (restrictionWeight k q c) g p.1.1.1 B Z

/-- The alternate split formula for the real Godement coefficient at a padded leading matrix. -/
def RealGapAlternateRestrictionStatement : Prop :=
  ∀ (_hk : 0 < k) (a : ℝˣ) (D' : RealQuotientMeasureData (k + q)) (η₁ : Measure H)
    (κ : Measure Compact), η₁.IsHaarMeasure → κ.IsHaarMeasure → κ.IsInvInvariant →
    ∃ C : ℝ≥0, 0 < C ∧
    ∀ (ds : List RealBlock) (c : RealCharacterData) (T : GodementColumnFactors k q)
      (Φ : 𝓢(Matrix I (Fin (k + q + 2)) ℝ, ℂ)),
      (∀ A x, Φ (joinLastColumn A x) = T.squareEval k q A * T.tail (Fin.last (q + 1)) x) →
    ∀ (U : G → ℂ), U ∈ realUniformWhittakerModel (k + q) ds (-a) → ∀ g : H,
      let μ := realSelfDualMeasure a
      let η := entryHaar μ (q + 1)
      let σ := outerMeasure k q μ η₁ κ
      let Fk := alternateRestrictionKernel k q a c T U g
      (∀ p, Integrable (Fk p) η) ∧ Integrable (fun p => ∫ Z, Fk p Z ∂η) σ ∧
      realAdjacentGodementCoefficient D' a Φ U c
          (padGL (Nat.succ_le_succ (Nat.le_succ (k + q))) (rankInclusion (q + 1) g)) =
        realAdjacentWeylSign (k + q) c * P g (1 / 2) * (C : ℂ) *
          ∫ p, (∫ Z, Fk p Z ∂η) ∂σ

set_option maxHeartbeats 800000 in
theorem realGapAlternateRestriction : RealGapAlternateRestrictionStatement k q := by
  intro hk a D' η₁ κ hη₁ hκ hκinv
  let μ := realSelfDualMeasure a
  let η := entryHaar μ (q + 1)
  let σ := outerMeasure k q μ η₁ κ
  let ξ := (rectangularMeasure μ k q).prod η
  let Haar := D'.groupHaar
  let : Haar.IsHaarMeasure := D'.groupHaar_isHaar
  let : κ.IsHaarMeasure := hκ
  let : η₁.IsHaarMeasure := hη₁
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let : SigmaFinite μ.measure := inferInstance
  let : SigmaFinite η := entryHaar_sigmaFinite μ _
  let : SigmaFinite (diagonalWeightMeasure k q) := inferInstance
  let : SecondCountableTopology N :=
    (Langlands.GeneralLinear.upperEntryCoordinates (K := ℝ) (q + 1)).secondCountableTopology
  let : SecondCountableTopology Compact := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : SigmaFinite σ := by
    unfold σ outerMeasure
    infer_instance
  let chart := triangularRightChart k q
  have hChart : Measurable chart := (continuous_triangularRightChart k q).measurable
  obtain ⟨C, hC, hHaar⟩ := RealGapTriangularChart.realGapTriangularChart k q hk μ Haar η₁ κ
    inferInstance hη₁ hκ hκinv
  change Haar = C • (σ.prod ξ).map chart at hHaar
  refine ⟨C, hC, ?_⟩
  intro ds c T Φ hΦ U hU g
  let g₀ : G := rankInclusion (q + 1) g
  let F := T.squareEval k q
  let Q := paddedRestrictionKernel c a F (T.tail (Fin.last (q + 1))) U g₀ 1
  let Fk := alternateRestrictionKernel k q a c T U g
  obtain ⟨hQ, hValue⟩ := realGodementPaddedRestriction (k + q) ds a D' c Φ F (T.tail (Fin.last (q + 1)))
    hΦ U hU g₀ 1
  change Integrable Q Haar at hQ
  have hMap : Integrable Q ((σ.prod ξ).map chart) := by
    rw [hHaar] at hQ
    exact (integrable_smul_measure (by exact_mod_cast hC.ne') ENNReal.coe_ne_top).mp hQ
  have hComp : Integrable (Q ∘ chart) (σ.prod ξ) :=
    (integrable_map_measure hMap.aestronglyMeasurable hChart.aemeasurable).mp hMap
  have hUeq : LeftWhittakerEquivariant k q a U :=
    fun u hu x => ((realUniformWhittakerRegularity (k + q) ds (-a) U hU).1 []).1 u hu x
  have hFiber (p : Outer k q) : Integrable (Fk p) η ∧
      (∫ u, Q (chart (p, u)) ∂ξ) = ∫ Z, Fk p Z ∂η := by
    obtain ⟨_, hI, hi⟩ := realGapTailExchange k q a (T.partial k q a) U hUeq
      (restrictionWeight k q c) g p.1.1.1 (retainedMatrix k q p)
    refine ⟨hI.const_mul _, ?_⟩
    simp only [show (fun u => Q (chart (p, u))) = ordinaryBlockTailKernel k q (T.partial k q a)
      U (restrictionWeight k q c) g p.1.1.1 (retainedMatrix k q p) from
        funext fun u => paddedRestrictionKernel_split k q a c T F (fun _ => rfl) U g p.1.1.1 (retainedMatrix k q p) u]
    rw [hi]
    exact (integral_const_mul _ _).symm
  have hIntegrable : Integrable (fun p => ∫ Z, Fk p Z ∂η) σ := by
    simp_rw [← (hFiber _).2]
    exact hComp.integral_prod_left
  have hInt : (∫ h, Q h ∂Haar) = (C : ℂ) * ∫ p, (∫ Z, Fk p Z ∂η) ∂σ := by
    rw [hHaar]
    change (∫ h, Q h ∂(C : ℝ≥0∞) • (σ.prod ξ).map chart) = _
    rw [integral_smul_measure, integral_map hChart.aemeasurable hMap.aestronglyMeasurable,
      ENNReal.coe_toReal, Complex.real_smul, integral_prod (fun x => Q (chart x)) hComp]
    simp_rw [(hFiber _).2]
  refine ⟨fun p => (hFiber p).1, hIntegrable, ?_⟩
  rw [mul_one] at hValue
  rw [hValue]
  have h1 : detCharacter c.character.toMonoidHom (1 : G) = 1 := by
    simp [detCharacter]
  have h2 : P (1 : G) (((k + q + 1 : ℕ) : ℂ) / 2) = 1 := by
    simp [ArchimedeanLocal.detPower, realNormalizedAbs]
  rw [h1, h2]
  change _ * _ * _ * _ * (∫ h, Q h ∂Haar) = _
  rw [hInt, show P g₀ (1 / 2) = P g (1 / 2) by
    unfold ArchimedeanLocal.detPower
    rw [det_rankInclusion]]
  ring

end Langlands.Global.RankinSelbergGlobal.RealGapAlternateRestriction
