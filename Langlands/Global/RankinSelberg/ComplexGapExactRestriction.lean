import Langlands.Global.RankinSelberg.ComplexGapRankCoordinates
import Langlands.Global.RankinSelberg.ComplexGapNormalizedRestriction
import Langlands.Global.RankinSelberg.ComplexGodementContinuedReflection
import Langlands.Global.RankinSelberg.ComplexJacquetChamberIntertwiner
import Langlands.Analysis.Local.QuotientMeasureExistence

/-! # The normalized Godement restrictions at the exact local points -/

noncomputable section

open MeasureTheory
open scoped NNReal Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapExactRestriction

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.GeneralLinear (determinant weylLong inverseTranspose)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.RankinSelberg (rectangularMeasure)
open ArchimedeanLocal (ComplexQuotientMeasureData complexNormalizedAbs complexSelfDualMeasure)
open ComplexGapAlternateRestriction (GodementColumnFactors)
open ComplexGapLeadingFourier (rectTransform)
open ComplexGapNormalizedRestriction (unitOrdinaryKernel unitDualKernel complexGapNormalizedRestriction)
open ComplexGapRankCoordinates (rankLT rectangleRows padGL_eq_consecutive rectangularPoint_eq_consecutive
  unfoldingWeyl_eq_consecutive tailWeyl_mul_self inverseTranspose_tailWeyl)
open ComplexGapSplitFourier (rectTransform_eq_complexRectangularFourier)
open ComplexGapUnitDeterminant (unitOuterMeasure)
open ComplexGapWeylRestriction (tailWeyl)
open ComplexGodementAddedCharacter (continuedValue complexGodementContinuedReflection)
open ComplexJacquetChamberIntertwiner (entryHaar_isMulRightInvariant)
open ComplexJacquetUnipotentMeasure (entryHaar entryHaar_isHaar)
open ComplexLocalWhittakerDual (dualData dualFunction_mem)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel
  archimedeanEquationComplexQMeasurable archimedeanEquationComplexQBorel

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs

open scoped Matrix.Norms.Operator in
/-- A quotient measure compatible with the prescribed full group and entry Haar measures. -/
theorem exists_entryHaar_quotient (r : ℕ) (μ : AdditiveHaarMeasure ℂ) :
    ∃ D : ComplexQuotientMeasureData r,
      D.groupHaar = complexGeneralLinearHaar (r + 1) ∧ D.unipotentHaar = entryHaar μ (r + 1) := by
  let H := Langlands.GeneralLinear.upperUnipotent (r + 1) ℂ
  let A := complexGeneralLinearHaar (r + 1)
  let B := entryHaar μ (r + 1)
  have hH : IsClosed (H : Set (G (r + 1))) := Langlands.GeneralLinear.UpperUnipotent.isClosed
  let : LocallyCompactSpace (G (r + 1)) := Units.isOpenEmbedding_val.locallyCompactSpace
  let : SecondCountableTopology (G (r + 1)) := Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let : SecondCountableTopology H := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : SigmaCompactSpace (G (r + 1)) := sigmaCompactSpace_of_locallyCompact_secondCountable
  let : SigmaCompactSpace H := sigmaCompactSpace_of_locallyCompact_secondCountable
  let : A.IsHaarMeasure := inferInstanceAs (complexGeneralLinearHaar _).IsHaarMeasure
  let : A.IsMulRightInvariant := inferInstanceAs (complexGeneralLinearHaar _).IsMulRightInvariant
  let : B.IsHaarMeasure := entryHaar_isHaar μ _
  let : B.IsMulRightInvariant := entryHaar_isMulRightInvariant μ r
  let : A.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure A
  let : B.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure B
  obtain ⟨ν, hν⟩ := Langlands.QuotientIntegration.compatibleMeasureExists H hH A B
  exact ⟨⟨A, inferInstance, B, inferInstance, inferInstance, ν, hν⟩, rfl, rfl⟩

variable (t q : ℕ)
local notation "k" => t + 1
local notation "n" => t + 1 + q + 1
local notation "H" => G (t + 1)
local notation "R" => Matrix (Fin (t + 1 + q + 1)) (Fin (t + 1 + q + 1 + 1)) ℂ
local notation "h" => rankLT t (q + 1)
local notation "FullLower" => Matrix (Fin (t + 1 + (q + 1) - (t + 1))) (Fin (t + 1)) ℂ
local notation "μ" => fun a => complexSelfDualMeasure a
local notation "Haar" => complexGeneralLinearHaar (t + 1 + q + 1)
local notation "κType" => unitaryCompact ℂ (t + 1 + q + 1)

/-- Right translate the Godement generator by the tail reversal appearing in the target. -/
def rotatedValue (a : ℂˣ) (d : ComplexCharacterData) (Φ : 𝓢(R, ℂ)) (W : G n → ℂ) (p : ℂ) :
    G (n + 1) → ℂ :=
  ArchimedeanLocal.translateFunction (tailWeyl k (q + 2)) (fun g => continuedValue Haar (μ a) d a Φ W g p)

private theorem dual_rotatedValue (a : ℂˣ) (d : ComplexCharacterData) (Φ : 𝓢(R, ℂ))
    (W : G n → ℂ) (p : ℂ) (g : G (n + 1)) :
    ArchimedeanLocal.dualFunction (n + 1) (rotatedValue t q a d Φ W p) (g * ArchimedeanLocal.unfoldingWeyl h) =
      ArchimedeanLocal.dualFunction (n + 1) (fun x => continuedValue Haar (μ a) d a Φ W x p) g := by
  let w : G (n + 1) := tailWeyl k (q + 2)
  let ι := inverseTranspose (n + 1) ℂ
  have hw : w * w = 1 := tailWeyl_mul_self k (q + 2)
  have hi : ι w = w := inverseTranspose_tailWeyl k (q + 2)
  have hW : ArchimedeanLocal.unfoldingWeyl h = w := unfoldingWeyl_eq_consecutive t (q + 1)
  unfold ArchimedeanLocal.dualFunction rotatedValue ArchimedeanLocal.translateFunction
  rw [hW]
  change continuedValue Haar (μ a) d a Φ W (weylLong (n + 1) ℂ * ι (g * w) * w) p =
    continuedValue Haar (μ a) d a Φ W (weylLong (n + 1) ℂ * ι g) p
  simp only [map_mul, hi, mul_assoc, hw, mul_one]

private theorem adjoiningSign_cancel (d : ComplexCharacterData) (m : ℕ) :
    (d.character ((-1 : ℂˣ) ^ m) : ℂ) * (d.inv.character ((-1 : ℂˣ) ^ m) : ℂ) = 1 := by
  rw [ComplexCharacterData.inv_character_apply]
  exact mul_inv_cancel₀ (d.character ((-1 : ℂˣ) ^ m)).ne_zero

/-- The exact ordinary and dual Godement values with a single chart constant. -/
def ComplexGapExactRestrictionStatement : Prop :=
  ∀ (a : ℂˣ) (κ : Measure κType), κ.IsHaarMeasure → κ.IsInvInvariant →
    ∃ c : ℝ≥0, 0 < c ∧
      ∀ (ds : List ComplexCharacterData), ds.length = n →
      ∀ (d : ComplexCharacterData) (Φ : 𝓢(R, ℂ))
        (T : GodementColumnFactors k q), (∀ X, Φ X = T.eval k q X) →
      ∀ (W : complexWhittakerModel (t + 1 + q) ds (-a)) (g : H) (p : ℂ),
        let σ := unitOuterMeasure k q (μ a) κ
        let η := entryHaar (μ a) (q + 1)
        let ρ := σ.prod ((rectangularMeasure (μ a) q k).prod η)
        let U := rotatedValue t q a d Φ W.val p
        let Ud := ArchimedeanLocal.dualFunction (n + 1) U
        let Wd := ArchimedeanLocal.dualFunction n W.val
        let F := unitOrdinaryKernel k q a d T W.val g p
        (Integrable (fun y => ∫ Z, F y Z ∂η) σ ∧
          U (padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) g) =
            (d.character (determinant (weylLong (q + 2) ℂ)) : ℂ) *
            (d.character ((-1 : ℂˣ) ^ n) : ℂ) * P g (1 / 2) * (c : ℂ) *
              ∫ y, (∫ Z, F y Z ∂η) ∂σ) ∧
        (∀ X : FullLower,
          let Fd := unitDualKernel k q a d Φ Wd g p (rectangleRows t (q + 1) X)
          Integrable Fd ρ ∧ Ud (ArchimedeanLocal.rectangularPoint h g X * ArchimedeanLocal.unfoldingWeyl h) =
            P g (1 / 2) * (c : ℂ) * ∫ y, Fd y ∂ρ)

/-- A right translate by the tail reversal cancels the same reversal in its dual. -/
theorem complexGapExactRestriction : ComplexGapExactRestrictionStatement t q := by
  intro a κ hκ hκinv
  obtain ⟨D, hDH, _⟩ := exists_entryHaar_quotient (t + 1 + q) (μ a)
  obtain ⟨c, hc, ho, hd⟩ := complexGapNormalizedRestriction k q (Nat.succ_pos t) a κ hκ hκinv
  refine ⟨c, hc, ?_⟩
  intro ds hds d Φ T hΦ W g p
  dsimp only
  obtain ⟨hi, he⟩ := ho ds d Φ T hΦ W g p
  refine ⟨⟨hi, ?_⟩, ?_⟩
  · rw [padGL_eq_consecutive]
    exact he
  · intro X
    let Wd : complexWhittakerModel (t + 1 + q) (dualData ds) a :=
      ⟨ArchimedeanLocal.dualFunction n W.val, by simpa only [neg_neg] using dualFunction_mem hds W.2⟩
    obtain ⟨hdi, hde⟩ := hd (dualData ds) d Φ Wd g p (rectangleRows t (q + 1) X)
    refine ⟨hdi, ?_⟩
    rw [dual_rotatedValue]
    have hR := complexGodementContinuedReflection D a d Φ (rectTransform a Φ)
      (rectTransform_eq_complexRectangularFourier k q a Φ) ds hds W (ArchimedeanLocal.rectangularPoint h g X) p
    rw [hDH] at hR
    rw [hR, rectangularPoint_eq_consecutive]
    rw [show ArchimedeanLocal.dualFunction n W.val = Wd.val from rfl, hde]
    simp only [← mul_assoc, adjoiningSign_cancel, one_mul]

end Langlands.Global.RankinSelbergGlobal.ComplexGapExactRestriction
