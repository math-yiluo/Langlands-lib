import Langlands.Global.RankinSelberg.ComplexGodementLowerRectangle
import Langlands.Global.RankinSelberg.ComplexUnequalFamilyKernels
import Langlands.Representation.RankinSelberg.AdjacentRankQuotientShear
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # The quotient change of variables in the complex Godement block integral -/

noncomputable section

open MeasureTheory Function
open scoped NNReal ENNReal SchwartzMap Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementBlockUnfolding

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.GeneralLinear (determinant)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure rectangularJoin)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.QuotientIntegration (rightTranslate continuous_rightTranslate_joint leftQuotient_isOpenQuotientMap)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure rectangularMeasure_isAddHaar)
open ArchimedeanLocal (complexNormalizedAbs complexUnequalIntegrand ComplexQuotientMeasureData)
open ComplexGodement (characterWeight normPower)
open ComplexGodementAddedCharacter (continuedValue)
open ComplexGodementLowerRectangle
open ComplexGodementPaddedRestriction (normPower_determinant)
open ComplexGodementPartialFourier (partialSchwartz)
open ComplexGodementTwoBlockRestriction
open ComplexTwoBlockHaar (rightTail rightTailWeight diagonalBlocks)
open ComplexUnequalFamily (HasLeftCharacter ordinaryKernel_mk)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "KU" => fun n => unitaryCompact ℂ n
local notation "Q" => fun t => LeftUnipotentQuotient t ℂ
local notation "N" => fun t => Langlands.GeneralLinear.upperUnipotent (t + 1) ℂ
local notation "Test" => fun r => SchwartzMap (Matrix (Fin (r + 1)) (Fin (r + 2)) ℂ) ℂ
local notation "XSpace" => fun r t => Matrix (Fin (r + 1 - (t + 1))) (Fin (t + 1)) ℂ
local notation "YSpace" => fun r t => Matrix (Fin (t + 1)) (Fin (r + 1 - (t + 1))) ℂ
local notation "Coords" => fun r t => ((G (t + 1) × G (r + 1 - (t + 1))) × YSpace r t) × KU (r + 1)
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs

local instance blockUnfoldingGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance blockUnfoldingGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance blockUnfoldingGLSecondCountable (n : ℕ) : SecondCountableTopology (G n) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) n).isInducing.secondCountableTopology
local instance blockUnfoldingGLLocallyCompact (n : ℕ) : LocallyCompactSpace (G n) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) n).locallyCompactSpace
attribute [local instance] ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel

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

private theorem detPower_mul {n : ℕ} (g b : G n) (s : ℂ) : P (g * b) s = P g s * P b s := by
  simp only [← normPower_determinant, map_mul]

section QuotientShift

variable {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [MeasurableSpace A] [BorelSpace A] (H : Subgroup A)
    [MeasurableSpace (Langlands.QuotientIntegration.LeftQuotient H)]
    [BorelSpace (Langlands.QuotientIntegration.LeftQuotient H)]
    [SecondCountableTopology (Langlands.QuotientIntegration.LeftQuotient H)]
    {S : Type} [MeasurableSpace S]

local notation "QH" => Langlands.QuotientIntegration.LeftQuotient H

private def quotientShift (k : S → A) (hk : Measurable k) : QH × S ≃ᵐ QH × S where
  toFun p := (rightTranslate H (k p.2) p.1, p.2)
  invFun p := (rightTranslate H ((k p.2)⁻¹) p.1, p.2)
  left_inv := by
    rintro ⟨q, p⟩
    change (rightTranslate H (k p)⁻¹ (rightTranslate H (k p) q), p) = (q, p)
    rw [Langlands.QuotientIntegration.rightTranslate_mul, mul_inv_cancel,
      Langlands.QuotientIntegration.rightTranslate_one]
  right_inv := by
    rintro ⟨q, p⟩
    change (rightTranslate H (k p) (rightTranslate H (k p)⁻¹ q), p) = (q, p)
    rw [Langlands.QuotientIntegration.rightTranslate_mul, inv_mul_cancel,
      Langlands.QuotientIntegration.rightTranslate_one]
  measurable_toFun := ((continuous_rightTranslate_joint H).measurable.comp
    (measurable_fst.prodMk (hk.comp measurable_snd))).prodMk measurable_snd
  measurable_invFun := ((continuous_rightTranslate_joint H).measurable.comp
    (measurable_fst.prodMk (hk.inv.comp measurable_snd))).prodMk measurable_snd

private theorem measurePreserving_quotientShift (τ : Measure QH) (ρ : Measure S)
    [SFinite ρ] [SFinite τ] (hInv : ∀ a : A, MeasurePreserving (rightTranslate H a) τ τ)
    (k : S → A) (hk : Measurable k) :
    MeasurePreserving (quotientShift H k hk) (τ.prod ρ) (τ.prod ρ) := by
  let e := quotientShift H k hk
  refine ⟨e.measurable, ?_⟩
  change (τ.prod ρ).map e = τ.prod ρ
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [lintegral_map hf e.measurable]
  change (∫⁻ p, (f ∘ e) p ∂τ.prod ρ) = ∫⁻ p, f p ∂τ.prod ρ
  rw [lintegral_prod_symm' _ (hf.comp e.measurable), lintegral_prod_symm' _ hf]
  apply lintegral_congr
  intro x
  let u := fun q => f (q, x)
  have hu : Measurable u := hf.comp (measurable_id.prodMk measurable_const)
  change (∫⁻ q, u (rightTranslate H (k x) q) ∂τ) = ∫⁻ q, u q ∂τ
  rw [← lintegral_map hu (hInv (k x)).measurable, (hInv (k x)).map_eq]

end QuotientShift

private theorem translate_hasLeftCharacter {r : ℕ} {a : ℂˣ} {W : G (r + 1) → ℂ}
    (hW : HasLeftCharacter a W) (k : G (r + 1)) :
    HasLeftCharacter a (ArchimedeanLocal.translateFunction k W) := by
  intro u g
  unfold ArchimedeanLocal.translateFunction
  rw [mul_assoc, hW]

private theorem model_hasLeftCharacter {r : ℕ} {ds : List ComplexCharacterData} {a : ℂˣ}
    (W : complexWhittakerModel r ds a) : HasLeftCharacter a W.val := by
  intro u g
  exact complexWhittakerModel_left_equivariant W.2 _ u.2 _

/-- The lower quotient kernel after the right shift of the smaller group variable. -/
def blockUnfoldedKernel {r t : ℕ} (h : t < r) (μ : AdditiveHaarMeasure ℂ)
    (d : ComplexCharacterData) (a : ℂˣ) (Φ : Test r) (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ)
    (s z : ℂ) (p : Q t × (XSpace r t × Coords r t)) : ℂ :=
  let X := p.2.1
  let v := p.2.2
  let k₁ := v.1.1.1
  let k₂ := rightTail (Nat.succ_pos t) (Nat.succ_lt_succ h) v.1.1.2 v.1.2 v.2
  let A := diagonalBlocks (Nat.succ_pos t) (Nat.succ_lt_succ h) k₁ 1
  let e : ℂ := ((r + 2 : ℕ) : ℂ) / 2 + s - 1
  let ω : ℂ := z - ((r - t : ℕ) : ℂ) / 2
  partialSchwartz a μ Φ (rectangularJoin (k₂.val * A.val * (lowerRectangle h X).val)
    (k₂⁻¹.val (Fin.last r))) * characterWeight d e (determinant k₂) *
    (characterWeight d e (determinant k₁) * P k₁ ω) *
    complexUnequalIntegrand h (ArchimedeanLocal.translateFunction k₂⁻¹ W)
      (ArchimedeanLocal.translateFunction k₁ V) z p.1

private def beforeBlockKernel {r t : ℕ} (h : t < r) (μ : AdditiveHaarMeasure ℂ)
    (d : ComplexCharacterData) (a : ℂˣ) (Φ : Test r) (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ)
    (s z : ℂ) (p : Q t × (XSpace r t × Coords r t)) : ℂ :=
  twoBlockRestrictionKernel (Nat.succ_pos t) (Nat.succ_lt_succ h) μ d a Φ W p.1.out
    (lowerRectangle h p.2.1) s p.2.2 * V p.1.out * P p.1.out (z - ((r - t : ℕ) : ℂ) / 2)

private theorem blockUnfoldedKernel_shift {r t : ℕ} (h : t < r) (μ : AdditiveHaarMeasure ℂ)
    (d : ComplexCharacterData) (a : ℂˣ) (Φ : Test r) (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ)
    (hW : HasLeftCharacter (-a) W) (hV : HasLeftCharacter a V) (s z : ℂ)
    (p : Q t × (XSpace r t × Coords r t)) :
    blockUnfoldedKernel h μ d a Φ W V s z
      (rightTranslate (N t) p.2.2.1.1.1⁻¹ p.1, p.2) =
        beforeBlockKernel h μ d a Φ W V s z p := by
  let q := p.1
  let k₁ := p.2.2.1.1.1
  let k₂ := rightTail (Nat.succ_pos t) (Nat.succ_lt_succ h) p.2.2.1.1.2 p.2.2.1.2 p.2.2.2
  let g := q.out
  have hq : rightTranslate (N t) k₁⁻¹ q = Quotient.mk _ (g * k₁⁻¹) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have hz : complexUnequalIntegrand h (ArchimedeanLocal.translateFunction k₂⁻¹ W)
      (ArchimedeanLocal.translateFunction k₁ V) z (rightTranslate (N t) k₁⁻¹ q) =
    W (padGL (Nat.succ_le_succ h.le) (g * k₁⁻¹) * k₂⁻¹) * V g *
      P (g * k₁⁻¹) (z - ((r - t : ℕ) : ℂ) / 2) := by
    rw [hq, ordinaryKernel_mk h (translate_hasLeftCharacter hW k₂⁻¹)
      (by simpa only [neg_neg] using translate_hasLeftCharacter hV k₁)]
    simp only [ArchimedeanLocal.translateFunction, inv_mul_cancel_right]
  let ω : ℂ := z - ((r - t : ℕ) : ℂ) / 2
  have hP : P k₁ ω * P (g * k₁⁻¹) ω = P g ω := by
    rw [mul_comm, ← detPower_mul, inv_mul_cancel_right]
  change _ * _ * (_ * P k₁ ω) * complexUnequalIntegrand h
      (ArchimedeanLocal.translateFunction k₂⁻¹ W)
      (ArchimedeanLocal.translateFunction k₁ V) z (rightTranslate (N t) k₁⁻¹ q) =
    _ * V g * P g ω
  rw [hz, ← hP]
  simp only [twoBlockRestrictionKernel]
  ring

/-- The block unfolding for the larger Godement value, under the joint absolute convergence
of its changed kernel. The lower quotient now pairs two right translates. -/
def ComplexGodementBlockUnfoldingStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (D : ComplexQuotientMeasureData t)
    (ν νX : AdditiveHaarMeasure ℂ) (κ : Measure (KU (r + 1))),
    κ.IsHaarMeasure → κ.IsInvInvariant → ∃ c : ℝ≥0, 0 < c ∧
    ∀ (ds : List ComplexCharacterData) (a : ℂˣ) (μ : AdditiveHaarMeasure ℂ)
      (d : ComplexCharacterData) (Φ : Test r) (W : complexWhittakerModel r ds (-a))
      (V : G (t + 1) → ℂ), HasLeftCharacter a V → ∀ (s z : ℂ),
      let η := (rectangularMeasure νX (r + 1 - (t + 1)) (t + 1)).prod
        (rightTailProductMeasure (r + 1) (t + 1) ν κ)
      let F := blockUnfoldedKernel h μ d a Φ W.val V s z
      Integrable F (D.measure.prod η) →
      ArchimedeanLocal.blockIntegral complexNormalizedAbs D.measure νX (Nat.lt_succ_of_lt h)
        (fun g => continuedValue (complexGeneralLinearHaar (r + 1)) μ d a Φ W.val g s) V z =
      ((d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) * (c : ℂ)) *
        ∫ p, ∫ q, F (q, p) ∂D.measure ∂η

set_option maxHeartbeats 1400000 in
theorem complexGodementBlockUnfolding : ComplexGodementBlockUnfoldingStatement := by
  intro r t h D ν νX κ hκ hκinv
  obtain ⟨c, hc, hPoint⟩ := complexGodementLowerRectangle r t h ν κ hκ hκinv
  refine ⟨c, hc, ?_⟩
  intro ds a μ d Φ W V hV s z
  let ρ := rightTailProductMeasure (r + 1) (t + 1) ν κ
  let σ := rectangularMeasure νX (r + 1 - (t + 1)) (t + 1)
  let η := σ.prod ρ
  let : κ.IsHaarMeasure := hκ
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  let : σ.IsAddHaarMeasure := rectangularMeasure_isAddHaar νX _ _
  have hσ : SigmaFinite σ := inferInstance
  let ρ₀ := (((complexGeneralLinearHaar (t + 1)).prod (complexGeneralLinearHaar (r + 1 - (t + 1)))).prod
    (rectangularMeasure ν (t + 1) (r + 1 - (t + 1)))).prod κ
  let : (rectangularMeasure ν (t + 1) (r + 1 - (t + 1))).IsAddHaarMeasure :=
    rectangularMeasure_isAddHaar ν _ _
  let : SigmaFinite ρ₀ := inferInstance
  let : SigmaFinite ρ := SigmaFinite.withDensity_of_ne_top (ae_of_all ρ₀
    fun (_ : Coords r t) => ENNReal.coe_ne_top)
  let : SigmaFinite σ := hσ
  let : SigmaFinite η := inferInstance
  let F := blockUnfoldedKernel h μ d a Φ W.val V s z
  let B := beforeBlockKernel h μ d a Φ W.val V s z
  let C : ℂ := (d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) * (c : ℂ)
  change Integrable F (D.measure.prod η) → _
  intro hF
  let k := fun p : XSpace r t × Coords r t => p.2.1.1.1
  have hk : Measurable k := measurable_fst.comp
    (measurable_fst.comp (measurable_fst.comp measurable_snd))
  let φ := (quotientShift (N t) k hk).symm
  have hφ : MeasurePreserving φ (D.measure.prod η) (D.measure.prod η) :=
    (measurePreserving_quotientShift (N t) D.measure η D.compatible.right_invariant k hk).symm _
  have hBF : F ∘ φ = B :=
    funext (blockUnfoldedKernel_shift h μ d a Φ W.val V (model_hasLeftCharacter W) hV s z)
  have hB : Integrable B (D.measure.prod η) :=
    hBF ▸ hφ.integrable_comp_of_integrable hF
  have hω : (1 / 2 : ℂ) + (z - ((r + 1 - t : ℕ) : ℂ) / 2) = z - ((r - t : ℕ) : ℂ) / 2 := by
    rw [show r + 1 - t = (r - t) + 1 by omega]
    push_cast
    ring
  calc
    _ = ∫ q, ∫ X, C * (∫ p, B (q, X, p) ∂ρ) ∂σ ∂D.measure := by
      unfold ArchimedeanLocal.blockIntegral
      apply integral_congr_ae
      refine ae_of_all _ fun q => ?_
      apply integral_congr_ae
      refine ae_of_all _ fun X => ?_
      unfold ArchimedeanLocal.blockKernel
      let g := q.out
      have hv := (hPoint ds a μ d Φ W g X s).2
      change continuedValue (complexGeneralLinearHaar (r + 1)) μ d a Φ W.val
            (ArchimedeanLocal.rectangularPoint (Nat.lt_succ_of_lt h) g X) s * V g *
          P g (z - ((r + 1 - t : ℕ) : ℂ) / 2) = _
      rw [hv]
      change _ = C * (∫ p, twoBlockRestrictionKernel (Nat.succ_pos t) (Nat.succ_lt_succ h)
        μ d a Φ W.val g (lowerRectangle h X) s p * V g *
          P g (z - ((r - t : ℕ) : ℂ) / 2) ∂ρ)
      rw [integral_mul_const, integral_mul_const]
      have hp := (detPower_add g (1 / 2) (z - ((r + 1 - t : ℕ) : ℂ) / 2)).symm
      rw [hω] at hp
      rw [← hp]
      unfold C
      ring
    _ = C * (∫ q, ∫ u, B (q, u) ∂η ∂D.measure) := by
      have hEq : (∫ q, ∫ X, ∫ p, B (q, X, p) ∂ρ ∂σ ∂D.measure) =
          ∫ q, ∫ u, B (q, u) ∂η ∂D.measure := by
        apply integral_congr_ae
        filter_upwards [hB.prod_right_ae] with q hq
        exact (integral_prod _ hq).symm
      simp_rw [integral_const_mul]
      rw [hEq]
    _ = C * (∫ p, ∫ q, F (q, p) ∂D.measure ∂η) := by
      rw [← integral_prod _ hB, ← hBF]
      change C * (∫ p, F (φ p) ∂D.measure.prod η) = _
      rw [hφ.integral_comp φ.measurableEmbedding F, integral_prod_symm _ hF]

end Langlands.Global.RankinSelbergGlobal.ComplexGodementBlockUnfolding
