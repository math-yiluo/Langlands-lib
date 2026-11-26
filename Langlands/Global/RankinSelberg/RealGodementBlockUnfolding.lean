import Langlands.Global.RankinSelberg.ComplexGodementBlockUnfolding
import Langlands.Global.RankinSelberg.RealGodementLowerRectangle
import Langlands.Global.RankinSelberg.RealGapAlternateWeighted
import Langlands.Representation.RankinSelberg.AdjacentRankQuotientShear
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # The quotient change of variables in the real Godement block integral -/

noncomputable section

open MeasureTheory Function
open scoped NNReal ENNReal SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodementBlockUnfolding

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (determinant)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.LocalFactor.Archimedean (RealBlock RealCharacterData)
open Langlands.QuotientIntegration (rightTranslate continuous_rightTranslate_joint leftQuotient_isOpenQuotientMap)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure rectangularMeasure_isAddHaar)
open ArchimedeanLocal (realNormalizedAbs realUnequalIntegrand RealQuotientMeasureData
  realFourierTransform)
open RealJacquet (realAdjacentGodementCoefficient realAdjacentWeylSign detCharacter realDetPower_mul
  joinLastColumn)
open RealGodementLowerRectangle
open RealGodementTwoBlockRestriction
open RealTwoBlockHaar (rightTail rightTailWeight diagonalBlocks)
open RealUnequalFamily (HasLeftCharacter)
open RealGapAlternateWeighted (ordinaryKernel_mk left_translate)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "KU" => fun n => unitaryCompact ℝ n
local notation "Q" => fun t => LeftUnipotentQuotient t ℝ
local notation "N" => fun t => Langlands.GeneralLinear.upperUnipotent (t + 1) ℝ
local notation "Test" => fun r => SchwartzMap (Matrix (Fin (r + 1)) (Fin (r + 2)) ℝ) ℂ
local notation "XSpace" => fun r t => Matrix (Fin (r + 1 - (t + 1))) (Fin (t + 1)) ℝ
local notation "YSpace" => fun r t => Matrix (Fin (t + 1)) (Fin (r + 1 - (t + 1))) ℝ
local notation "Coords" => fun r t => ((G (t + 1) × G (r + 1 - (t + 1))) × YSpace r t) × KU (r + 1)
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs

local instance blockUnfoldingGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance blockUnfoldingGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance blockUnfoldingMatrixSecondCountable (m n : ℕ) :
    SecondCountableTopology (Matrix (Fin m) (Fin n) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
local instance blockUnfoldingGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n ℝ) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) n).isInducing.secondCountableTopology
local instance blockUnfoldingGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear n ℝ) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) n).locallyCompactSpace
local instance blockUnfoldingNMeasurable (t : ℕ) : MeasurableSpace (N t) := borel _
local instance blockUnfoldingNBorel (t : ℕ) : BorelSpace (N t) := ⟨rfl⟩
local instance blockUnfoldingQMeasurable (t : ℕ) : MeasurableSpace (Q t) := borel _
local instance blockUnfoldingQBorel (t : ℕ) : BorelSpace (Q t) := ⟨rfl⟩

local instance blockUnfoldingQSecondCountable (t : ℕ) : SecondCountableTopology (Q t) :=
  TopologicalSpace.Quotient.secondCountableTopology (leftQuotient_isOpenQuotientMap (N t)).isOpenMap
local instance blockUnfoldingQSigmaCompact (t : ℕ) : SigmaCompactSpace (Q t) := by
  let : SigmaCompactSpace (G (t + 1)) := sigmaCompactSpace_of_locallyCompact_secondCountable
  let e := leftQuotient_isOpenQuotientMap (N t)
  apply isSigmaCompact_univ_iff.mp
  rw [← Set.range_eq_univ.mpr e.surjective]
  exact isSigmaCompact_range e.continuous

private theorem detPower_add {n : ℕ} (g : G n) (s z : ℂ) :
    P g (s + z) = P g s * P g z := by
  unfold ArchimedeanLocal.detPower
  rw [add_mul, Complex.exp_add]

private theorem detPower_mul {n : ℕ} (g b : G n) (s : ℂ) : P (g * b) s = P g s * P b s :=
  realDetPower_mul g b s

/-- The lower quotient kernel after the right shift of the smaller group variable. -/
def blockUnfoldedKernel {r t : ℕ} (h : t < r) (c : RealCharacterData) (a : ℝˣ)
    (F : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ → ℂ) (f : (Fin (r + 1) → ℝ) → ℂ)
    (U : G (r + 1) → ℂ) (V : G (t + 1) → ℂ)
    (z : ℂ) (p : Q t × (XSpace r t × Coords r t)) : ℂ :=
  let X := p.2.1
  let v := p.2.2
  let k₁ := v.1.1.1
  let k₂ := rightTail (Nat.succ_pos t) (Nat.succ_lt_succ h) v.1.1.2 v.1.2 v.2
  let A := diagonalBlocks (Nat.succ_pos t) (Nat.succ_lt_succ h) k₁ 1
  let η := c.character.toMonoidHom
  let ω : ℂ := z - ((r - t : ℕ) : ℂ) / 2
  F (k₂ * A * lowerRectangle h X).val * realFourierTransform a f (Langlands.RankinSelberg.lastRow k₂⁻¹) *
    (detCharacter η k₂ * P k₂ ((r : ℂ) / 2)) *
    ((detCharacter η k₁ * P k₁ ((r : ℂ) / 2)) * P k₁ ω) *
    realUnequalIntegrand h (ArchimedeanLocal.translateFunction k₂⁻¹ U)
      (ArchimedeanLocal.translateFunction k₁ V) z p.1

/-- The right-tail block kernel before shearing the quotient coordinate. -/
def beforeBlockKernel {r t : ℕ} (h : t < r) (c : RealCharacterData) (a : ℝˣ)
    (F : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ → ℂ) (f : (Fin (r + 1) → ℝ) → ℂ)
    (U : G (r + 1) → ℂ) (V : G (t + 1) → ℂ)
    (z : ℂ) (p : Q t × (XSpace r t × Coords r t)) : ℂ :=
  twoBlockRestrictionKernel (Nat.succ_pos t) (Nat.succ_lt_succ h) c a F f U p.1.out
    (lowerRectangle h p.2.1) p.2.2 * V p.1.out * P p.1.out (z - ((r - t : ℕ) : ℂ) / 2)

/-- The two block kernels are related by the right quotient shear. -/
theorem blockUnfoldedKernel_shift {r t : ℕ} (h : t < r) (c : RealCharacterData) (a : ℝˣ)
    (F : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ → ℂ) (f : (Fin (r + 1) → ℝ) → ℂ)
    (U : G (r + 1) → ℂ) (V : G (t + 1) → ℂ)
    (hW : HasLeftCharacter (-a) U) (hV : HasLeftCharacter a V) (z : ℂ)
    (p : Q t × (XSpace r t × Coords r t)) :
    blockUnfoldedKernel h c a F f U V z
      (rightTranslate (N t) p.2.2.1.1.1⁻¹ p.1, p.2) =
        beforeBlockKernel h c a F f U V z p := by
  let q := p.1
  let k₁ := p.2.2.1.1.1
  let k₂ := rightTail (Nat.succ_pos t) (Nat.succ_lt_succ h) p.2.2.1.1.2 p.2.2.1.2 p.2.2.2
  let g := q.out
  have hq : rightTranslate (N t) k₁⁻¹ q = Quotient.mk _ (g * k₁⁻¹) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have hz : realUnequalIntegrand h (ArchimedeanLocal.translateFunction k₂⁻¹ U)
      (ArchimedeanLocal.translateFunction k₁ V) z (rightTranslate (N t) k₁⁻¹ q) =
    U (padGL (Nat.succ_le_succ h.le) (g * k₁⁻¹) * k₂⁻¹) * V g *
      P (g * k₁⁻¹) (z - ((r - t : ℕ) : ℂ) / 2) := by
    rw [hq, ordinaryKernel_mk h (left_translate hW k₂⁻¹)
      (by simpa only [neg_neg] using left_translate hV k₁)]
    simp only [ArchimedeanLocal.translateFunction, inv_mul_cancel_right]
  let ω : ℂ := z - ((r - t : ℕ) : ℂ) / 2
  have hP : P k₁ ω * P (g * k₁⁻¹) ω = P g ω := by
    rw [mul_comm, ← detPower_mul, inv_mul_cancel_right]
  change _ * _ * _ * (_ * P k₁ ω) * realUnequalIntegrand h
      (ArchimedeanLocal.translateFunction k₂⁻¹ U)
      (ArchimedeanLocal.translateFunction k₁ V) z (rightTranslate (N t) k₁⁻¹ q) =
    _ * V g * P g ω
  rw [hz, ← hP]
  simp only [twoBlockRestrictionKernel]
  ring

/-- The block unfolding for the larger Godement coefficient, under the joint absolute
convergence of its changed kernel. The lower quotient now pairs two right translates. -/
def RealGodementBlockUnfoldingStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (D : RealQuotientMeasureData t) (D' : RealQuotientMeasureData r)
    (ν νX : AdditiveHaarMeasure ℝ) (μ₁ : Measure (G (t + 1))) (μ₂ : Measure (G (r + 1 - (t + 1))))
    (κ : Measure (KU (r + 1))),
    μ₁.IsHaarMeasure → μ₂.IsHaarMeasure → κ.IsHaarMeasure → κ.IsInvInvariant → ∃ C : ℝ≥0, 0 < C ∧
    ∀ (ds : List RealBlock) (a : ℝˣ) (c : RealCharacterData)
      (Φ : 𝓢(Matrix (Fin (r + 1)) (Fin (r + 2)) ℝ, ℂ))
      (F : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ → ℂ) (f : (Fin (r + 1) → ℝ) → ℂ),
      (∀ A x, Φ (joinLastColumn A x) = F A * f x) →
    ∀ (U : G (r + 1) → ℂ), U ∈ realUniformWhittakerModel r ds (-a) →
      ∀ (V : G (t + 1) → ℂ), HasLeftCharacter a V → ∀ z : ℂ,
      let η := (rectangularMeasure νX (r + 1 - (t + 1)) (t + 1)).prod
        (rightTailProductMeasure (r + 1) (t + 1) ν μ₁ μ₂ κ)
      let Fk := blockUnfoldedKernel h c a F f U V z
      Integrable Fk (D.measure.prod η) →
      ArchimedeanLocal.blockIntegral realNormalizedAbs D.measure νX (Nat.lt_succ_of_lt h)
        (realAdjacentGodementCoefficient D' a Φ U c) V z =
      (realAdjacentWeylSign r c * (C : ℂ)) * ∫ p, ∫ q, Fk (q, p) ∂D.measure ∂η

set_option maxHeartbeats 1400000 in
theorem realGodementBlockUnfolding : RealGodementBlockUnfoldingStatement := by
  intro r t h D D' ν νX μ₁ μ₂ κ hμ₁ hμ₂ hκ hκinv
  obtain ⟨C, hC, hPoint⟩ := realGodementLowerRectangle r t h ν μ₁ μ₂ κ hμ₁ hμ₂ hκ hκinv D'
  refine ⟨C, hC, ?_⟩
  intro ds a c Φ F f hΦ U hU V hV z
  let ρ := rightTailProductMeasure (r + 1) (t + 1) ν μ₁ μ₂ κ
  let σ := rectangularMeasure νX (r + 1 - (t + 1)) (t + 1)
  let η := σ.prod ρ
  let : κ.IsHaarMeasure := hκ
  let : μ₁.IsHaarMeasure := hμ₁
  let : μ₂.IsHaarMeasure := hμ₂
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  let : σ.IsAddHaarMeasure := rectangularMeasure_isAddHaar νX _ _
  have hσ : SigmaFinite σ := inferInstance
  let ρ₀ := ((μ₁.prod μ₂).prod (rectangularMeasure ν (t + 1) (r + 1 - (t + 1)))).prod κ
  let : (rectangularMeasure ν (t + 1) (r + 1 - (t + 1))).IsAddHaarMeasure :=
    rectangularMeasure_isAddHaar ν _ _
  let : SigmaFinite ρ₀ := inferInstance
  let : SigmaFinite ρ := SigmaFinite.withDensity_of_ne_top (ae_of_all ρ₀
    fun (_ : Coords r t) => ENNReal.coe_ne_top)
  let : SigmaFinite σ := hσ
  let : SigmaFinite η := inferInstance
  let Fk := blockUnfoldedKernel h c a F f U V z
  let B := beforeBlockKernel h c a F f U V z
  let C' : ℂ := realAdjacentWeylSign r c * (C : ℂ)
  change Integrable Fk (D.measure.prod η) → _
  intro hF
  let k := fun p : XSpace r t × Coords r t => p.2.1.1.1
  have hk : Measurable k := measurable_fst.comp
    (measurable_fst.comp (measurable_fst.comp measurable_snd))
  let φ := (ComplexGodementBlockUnfolding.quotientShift (N t) k hk).symm
  have hφ : MeasurePreserving φ (D.measure.prod η) (D.measure.prod η) :=
    (ComplexGodementBlockUnfolding.measurePreserving_quotientShift (N t) D.measure η D.compatible.right_invariant k hk).symm _
  have hBF : Fk ∘ φ = B :=
    funext (blockUnfoldedKernel_shift h c a F f U V
      (RealGapAlternateWeighted.leftCharacter_of_mem hU) hV z)
  have hB : Integrable B (D.measure.prod η) :=
    hBF ▸ hφ.integrable_comp_of_integrable hF
  have hω : (1 / 2 : ℂ) + (z - ((r + 1 - t : ℕ) : ℂ) / 2) = z - ((r - t : ℕ) : ℂ) / 2 := by
    rw [show r + 1 - t = (r - t) + 1 by omega]
    push_cast
    ring
  calc
    _ = ∫ q, ∫ X, C' * (∫ p, B (q, X, p) ∂ρ) ∂σ ∂D.measure := by
      unfold ArchimedeanLocal.blockIntegral
      apply integral_congr_ae
      refine ae_of_all _ fun q => ?_
      apply integral_congr_ae
      refine ae_of_all _ fun X => ?_
      unfold ArchimedeanLocal.blockKernel
      let g := q.out
      have hv := (hPoint ds a c Φ F f hΦ U hU g X).2
      change realAdjacentGodementCoefficient D' a Φ U c
            (ArchimedeanLocal.rectangularPoint (Nat.lt_succ_of_lt h) g X) * V g *
          P g (z - ((r + 1 - t : ℕ) : ℂ) / 2) = _
      rw [hv]
      change _ = C' * (∫ p, twoBlockRestrictionKernel (Nat.succ_pos t) (Nat.succ_lt_succ h)
        c a F f U g (lowerRectangle h X) p * V g *
          P g (z - ((r - t : ℕ) : ℂ) / 2) ∂ρ)
      rw [integral_mul_const, integral_mul_const]
      have hp := (detPower_add g (1 / 2) (z - ((r + 1 - t : ℕ) : ℂ) / 2)).symm
      rw [hω] at hp
      rw [← hp]
      unfold C'
      ring
    _ = C' * (∫ q, ∫ u, B (q, u) ∂η ∂D.measure) := by
      have hEq : (∫ q, ∫ X, ∫ p, B (q, X, p) ∂ρ ∂σ ∂D.measure) =
          ∫ q, ∫ u, B (q, u) ∂η ∂D.measure := by
        apply integral_congr_ae
        filter_upwards [hB.prod_right_ae] with q hq
        exact (integral_prod _ hq).symm
      simp_rw [integral_const_mul]
      rw [hEq]
    _ = C' * (∫ p, ∫ q, Fk (q, p) ∂D.measure ∂η) := by
      rw [← integral_prod _ hB, ← hBF]
      change C' * (∫ p, Fk (φ p) ∂D.measure.prod η) = _
      rw [hφ.integral_comp φ.measurableEmbedding Fk, integral_prod_symm _ hF]

end Langlands.Global.RankinSelbergGlobal.RealGodementBlockUnfolding
