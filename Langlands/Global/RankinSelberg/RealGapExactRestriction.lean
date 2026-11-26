import Langlands.Global.RankinSelberg.RealGapRankCoordinates
import Langlands.Global.RankinSelberg.RealGapNormalizedRestriction
import Langlands.Global.RankinSelberg.RealGodementColumnReflection

/-! # The normalized real Godement restrictions at the exact local points -/

noncomputable section

open MeasureTheory
open scoped NNReal SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapExactRestriction

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (determinant weylLong inverseTranspose rankInclusion)
open Langlands.LocalFactor.Archimedean (RealBlock RealCharacterData)
open Langlands.RankinSelberg (rectangularMeasure)
open ArchimedeanLocal (realSelfDualMeasure realNormalizedAbs RealQuotientMeasureData)
open RealJacquet (realAdjacentGodementCoefficient realAdjacentWeylSign detCharacter realColumnProduct)
open RealGapAlternateRestriction (GodementColumnFactors)
open RealGapNormalizedRestriction (unitOrdinaryKernel unitDualKernel realGapNormalizedRestriction)
open RealGapRankCoordinates (rankLT rectangleRows padGL_eq_consecutive rectangularPoint_eq_consecutive
  unfoldingWeyl_eq_consecutive tailWeyl_mul_self inverseTranspose_tailWeyl)
open RealGapUnitDeterminant (unitOuterMeasure)
open RealGapWeylRestriction (tailWeyl)
open RealGodement (realRectangularSchwartzFourier realRowSchwartzFourier godementColumnValue
  realGodementColumnReflection)
open RealGodementPaddedRestriction (realColumnProduct_joinLastColumn)
open RealJacquetUnipotentMeasure (entryHaar)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs

local instance gapGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance gapGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance gapNUMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := borel _
local instance gapNUBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩

/-- The dual of a real Godement coefficient is the Godement coefficient of the transformed test
for the opposite character, the dual lower function and the inverse character datum. -/
theorem dual_realAdjacentGodementCoefficient {r : ℕ} (D : RealQuotientMeasureData r) (a : ℝˣ)
    (Φ : 𝓢(Matrix (Fin (r + 1)) (Fin (r + 2)) ℝ, ℂ)) (c : RealCharacterData) (ds dds : List RealBlock)
    (U : G (r + 1) → ℂ) (hU : U ∈ realUniformWhittakerModel r ds (-a))
    (hUd : ArchimedeanLocal.dualFunction (r + 1) U ∈ realUniformWhittakerModel r dds a)
    (g : G (r + 2)) :
    ArchimedeanLocal.dualFunction (r + 2) (realAdjacentGodementCoefficient D a Φ U c) g =
      (c.character ((-1 : ℝˣ) ^ (r + 1)) : ℂ) *
        realAdjacentGodementCoefficient D (-a) (realRectangularSchwartzFourier a Φ)
          (ArchimedeanLocal.dualFunction (r + 1) U) c.inverse g := by
  let w := weylLong (r + 2) ℝ
  have h := (realGodementColumnReflection r D a Φ c ds dds U (w * g) hU hUd).2.2
  have he : Langlands.GeneralLinear.weylInverseTranspose (r + 2) ℝ (w * g) =
      inverseTranspose (r + 2) ℝ g := by
    simp only [w, Langlands.GeneralLinear.weylInverseTranspose_apply, map_mul,
      Langlands.GeneralLinear.inverseTranspose_weylLong, ← mul_assoc,
      Langlands.GeneralLinear.weylLong_mul_self, one_mul]
  rw [he] at h
  change godementColumnValue D a Φ U c (w * (w * inverseTranspose (r + 2) ℝ g)) = _
  rwa [← mul_assoc, Langlands.GeneralLinear.weylLong_mul_self, one_mul]

variable (t q : ℕ)
local notation "k" => t + 1
local notation "n" => t + 1 + q + 1
local notation "H" => G (t + 1)
local notation "Sq" => Matrix (Fin (t + 1 + q + 1)) (Fin (t + 1 + q + 1)) ℝ
local notation "h" => rankLT t (q + 1)
local notation "FullLower" => Matrix (Fin (t + 1 + (q + 1) - (t + 1))) (Fin (t + 1)) ℝ
local notation "κType" => unitaryCompact ℝ (t + 1 + q + 1)

/-- The separated Godement generator translated on the right by the tail reversal. -/
def rotatedValue (a : ℝˣ) (D' : RealQuotientMeasureData (t + 1 + q)) (c : RealCharacterData)
    (F : 𝓢(Sq, ℂ)) (T : GodementColumnFactors k q) (U : G n → ℂ) : G (n + 1) → ℂ :=
  ArchimedeanLocal.translateFunction (tailWeyl k (q + 2))
    (realAdjacentGodementCoefficient D' a (realColumnProduct F (T.tail (Fin.last (q + 1)))) U c)

private theorem dual_rotatedValue (a : ℝˣ) (D' : RealQuotientMeasureData (t + 1 + q))
    (c : RealCharacterData) (F : 𝓢(Sq, ℂ)) (T : GodementColumnFactors k q) (U : G n → ℂ)
    (g : G (n + 1)) :
    ArchimedeanLocal.dualFunction (n + 1) (rotatedValue t q a D' c F T U)
        (g * ArchimedeanLocal.unfoldingWeyl h) =
      ArchimedeanLocal.dualFunction (n + 1)
        (realAdjacentGodementCoefficient D' a (realColumnProduct F (T.tail (Fin.last (q + 1)))) U c) g := by
  let w : G (n + 1) := tailWeyl k (q + 2)
  let ι := inverseTranspose (n + 1) ℝ
  have hw : w * w = 1 := tailWeyl_mul_self k (q + 2)
  have hi : ι w = w := inverseTranspose_tailWeyl k (q + 2)
  have hW : ArchimedeanLocal.unfoldingWeyl h = w := unfoldingWeyl_eq_consecutive t (q + 1)
  unfold ArchimedeanLocal.dualFunction rotatedValue ArchimedeanLocal.translateFunction
  rw [hW]
  change realAdjacentGodementCoefficient D' a (realColumnProduct F (T.tail (Fin.last (q + 1)))) U c
      (weylLong (n + 1) ℝ * ι (g * w) * w) =
    realAdjacentGodementCoefficient D' a (realColumnProduct F (T.tail (Fin.last (q + 1)))) U c
      (weylLong (n + 1) ℝ * ι g)
  simp only [map_mul, hi, mul_assoc, hw, mul_one]

/-- The exact ordinary and dual Godement values with a single chart constant. -/
def RealGapExactRestrictionStatement : Prop :=
  ∀ (a : ℝˣ) (D' : RealQuotientMeasureData (t + 1 + q)) (η₁ : Measure H) (κ : Measure κType),
    η₁.IsHaarMeasure → κ.IsHaarMeasure → κ.IsInvInvariant →
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (ds dds : List RealBlock) (c : RealCharacterData) (F : 𝓢(Sq, ℂ))
        (T : GodementColumnFactors k q), (∀ B, F B = T.squareEval k q B) →
      ∀ (U : G n → ℂ), U ∈ realUniformWhittakerModel (t + 1 + q) ds (-a) →
        ArchimedeanLocal.dualFunction n U ∈ realUniformWhittakerModel (t + 1 + q) dds a →
      ∀ g : H,
        let μ := realSelfDualMeasure a
        let σ := unitOuterMeasure k q μ η₁ κ
        let η := entryHaar μ (q + 1)
        let ρ := σ.prod ((rectangularMeasure μ q k).prod η)
        let W := rotatedValue t q a D' c F T U
        let Wd := ArchimedeanLocal.dualFunction (n + 1) W
        let Ud := ArchimedeanLocal.dualFunction n U
        let Fo := unitOrdinaryKernel k q a c T U g
        (Integrable (fun y => ∫ Z, Fo y Z ∂η) σ ∧
          W (padGL (Nat.le_of_lt (Nat.succ_lt_succ h)) g) =
            detCharacter c.character.toMonoidHom (weylLong (q + 2) ℝ) *
              realAdjacentWeylSign (t + 1 + q) c * P g (1 / 2) * (C : ℂ) *
                ∫ y, (∫ Z, Fo y Z ∂η) ∂σ) ∧
        (∀ X : FullLower,
          let Fd := unitDualKernel k q a c F T Ud g (rectangleRows t (q + 1) X)
          Integrable Fd ρ ∧
            Wd (ArchimedeanLocal.rectangularPoint h g X * ArchimedeanLocal.unfoldingWeyl h) =
              (c.character ((-1 : ℝˣ) ^ n) : ℂ) * realAdjacentWeylSign (t + 1 + q) c.inverse *
                P g (1 / 2) * (C : ℂ) * ∫ y, Fd y ∂ρ)

theorem realGapExactRestriction : RealGapExactRestrictionStatement t q := by
  intro a D' η₁ κ hη₁ hκ hκinv
  obtain ⟨C, hC, ho, hd⟩ := realGapNormalizedRestriction k q (Nat.succ_pos t) a D' η₁ κ hη₁ hκ hκinv
  refine ⟨C, hC, ?_⟩
  intro ds dds c F T hF U hU hUd g
  dsimp only
  have hΦ : ∀ B x, realColumnProduct F (T.tail (Fin.last (q + 1))) (RealJacquet.joinLastColumn B x) =
      T.squareEval k q B * T.tail (Fin.last (q + 1)) x := fun B x => by
    rw [realColumnProduct_joinLastColumn, hF]
  obtain ⟨hi, he⟩ := ho ds c T (realColumnProduct F (T.tail (Fin.last (q + 1)))) hΦ U hU g
  refine ⟨⟨hi, ?_⟩, ?_⟩
  · unfold rotatedValue ArchimedeanLocal.translateFunction
    rw [padGL_eq_consecutive]
    exact he
  · intro X
    obtain ⟨hdi, hde⟩ := hd dds c F T hF (ArchimedeanLocal.dualFunction n U) hUd g
      (rectangleRows t (q + 1) X)
    refine ⟨hdi, ?_⟩
    rw [dual_rotatedValue, dual_realAdjacentGodementCoefficient D' a _ c ds dds U hU hUd,
      RealJacquet.realColumnProduct_fourier, rectangularPoint_eq_consecutive, hde]
    ring

end Langlands.Global.RankinSelbergGlobal.RealGapExactRestriction
