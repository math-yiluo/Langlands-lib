import Langlands.Global.RankinSelberg.RealGapDualArguments
import Langlands.Global.RankinSelberg.RealGapSplitFourier

/-! # Matching the split tests in the two real Godement integrals -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapMatchedTests

open Langlands.GeneralLinear (rankInclusion inverseTranspose determinant)
open Langlands.LocalFactor.Archimedean (RealCharacterData)
open Langlands.RankinSelberg (rectangularMeasure)
open ArchimedeanLocal (realSelfDualMeasure realNormalizedAbs realFourierTransform)
open RealGapAlternateRestriction (GodementColumnFactors restrictionWeight)
open RealGapDualArguments (leading tailColumn dualMatrix lowerPoint shearRectangle
  leadingArgument tailArgument lastFrequency whittakerArgument measurePreserving_shearRectangle)
open RealGapDualChart (lowerShear)
open RealGapLeadingFourier (leadingRestriction stackRows rectTransform rectFourier
  realGapLeadingFourier integrable_rectTransform_complement)
open RealGapSplitFourier (fourierFactors realGapSplitFourier)
open RealGapColumnFourier (columnSchwartzFourier columnSchwartzFourier_apply)
open RealGapTailExchange (alternateBlockTailKernel fixedTailFactor)
open RealGapUpperTail (packedTail)
open RealGapWeylRestriction (reverseTail tailWeyl)
open RealGodementPaddedRestriction (paddedRestrictionKernel)
open RealGodement (realRectangularSchwartzFourier realRowSchwartzFourier realRowSchwartzFourier_apply
  realRowSchwartzFourier_neg_comp)

variable (k q : ℕ)
local notation "I" => Fin (k + q + 1)
local notation "J" => Fin (q + 1)
local notation "G" => Langlands.GeneralLinear (k + q + 1) ℝ
local notation "H" => Langlands.GeneralLinear k ℝ
local notation "A" => rankInclusion (R := ℝ) (n := k) (q + 1)
local notation "ι" => inverseTranspose (k + q + 1) ℝ
local notation "ι₁" => inverseTranspose k ℝ
local notation "w" => tailWeyl k (q + 1)
local notation "Sq" => Matrix I I ℝ
local notation "U" => Matrix (Fin q) (Fin k) ℝ
local notation "FullLower" => Matrix J (Fin k) ℝ
local notation "row" => Langlands.RankinSelberg.lastRow
local notation "Fcol" => realFourierTransform

/-- The shared tail contribution after matching the rotated ordinary test and the dual test. -/
def tailFactor (a : ℝˣ) (T : GodementColumnFactors k q) (C : G) : ℂ :=
  T.tail (Fin.last (q + 1)) (tailColumn k q C 0) *
    ∏ j : J, Fcol a (T.tail j.rev.castSucc) (tailColumn k q (ι C) j)

private theorem lastFrequency_inverseTranspose (C : G) : row C⁻¹ = tailColumn k q (ι C) (Fin.last q) := by
  funext i
  have he : (Fin.last q).natAdd k = Fin.last (k + q) := Fin.ext rfl
  change C⁻¹.val (Fin.last (k + q)) i = C⁻¹.val ((Fin.last q).natAdd k) i
  rw [he]

private theorem rev_index (j : Fin q) : j.castSucc.rev.castSucc = j.succ.castSucc.rev := by
  apply Fin.ext
  simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_rev]
  omega

/-- In ordinary coordinates the head column and final frequency precede the later Fourier factors. -/
theorem tailFactor_reverse (a : ℝˣ) (T : GodementColumnFactors k q) (C : G) :
    tailFactor k q a T C =
      T.tail (Fin.last (q + 1)) (tailColumn k q C 0) *
        Fcol a (T.tail 0) (row C⁻¹) *
          ∏ j : Fin q, Fcol a (T.tail j.succ.castSucc.rev) (tailColumn k q (ι C) j.castSucc) := by
  unfold tailFactor
  rw [Fin.prod_univ_castSucc]
  simp only [rev_index, Fin.rev_last, Fin.castSucc_zero, ← lastFrequency_inverseTranspose]
  ring

/-- The split alternate kernel of the reversed factors has the shared tail factor. -/
theorem alternateBlockTailKernel_reverse (a : ℝˣ) (T : GodementColumnFactors k q) (W : G → ℂ)
    (χ : ℝˣ →* ℂ) (g h : H) (B : G) (Z : Langlands.GeneralLinear.upperUnipotent (q + 1) ℝ) :
    let C := B * (packedTail k q 0 Z).val
    alternateBlockTailKernel k q a ((reverseTail k q T).partial k q a) W χ g h B Z =
      T.leading (leading k q (C * A h)) * tailFactor k q a T C *
        W (A (g * h⁻¹) * C⁻¹) * χ (determinant h) * χ (determinant C) := by
  intro C
  rw [tailFactor_reverse]
  unfold alternateBlockTailKernel fixedTailFactor GodementColumnFactors.partial reverseTail
  simp only [Fin.rev_zero, Fin.rev_last]
  change (T.leading (leading k q (C * A h)) * T.tail (Fin.last (q + 1)) (tailColumn k q C 0) *
    Fcol a (T.tail 0) (row C⁻¹) * W (A (g * h⁻¹) * C⁻¹) * χ (determinant h) * χ (determinant C)) *
      (∏ j : Fin q, Fcol a (T.tail j.succ.castSucc.rev) (tailColumn k q (ι C) j.castSucc)) = _
  ring

private theorem tailProduct_rev (a : ℝˣ) (T : GodementColumnFactors k q) (C : G) :
    (∏ j : J, Fcol a (T.tail j.castSucc) (tailColumn k q (ι C) j.rev)) =
      ∏ j : J, Fcol a (T.tail j.rev.castSucc) (tailColumn k q (ι C) j) := by
  refine Fintype.prod_equiv (Fin.revPerm : Equiv.Perm J) _ _ ?_
  intro j
  change Fcol a (T.tail j.castSucc) _ = Fcol a (T.tail j.rev.rev.castSucc) _
  rw [Fin.rev_rev]
  rfl

/-- The real padded dual kernel before integration in its complementary rectangle: the
padded restriction kernel of the transformed separated test at `-a` for the inverse character. -/
def dualFiber (a : ℝˣ) (c : RealCharacterData) (F : 𝓢(Sq, ℂ)) (T : GodementColumnFactors k q)
    (Ud : G → ℂ) (g h : H) (C : G) (V : U) (X : FullLower) : ℂ :=
  paddedRestrictionKernel c.inverse (-a) (realRectangularSchwartzFourier a F)
    (realRowSchwartzFourier (k + q + 1) a (T.tail (Fin.last (q + 1)))) Ud (A g) (lowerShear k q X)
    (dualMatrix k q C h V)

/-- The factor independent of the complementary rectangle in the dual integral. -/
def dualFiberFactor (a : ℝˣ) (c : RealCharacterData) (T : GodementColumnFactors k q)
    (Ud : G → ℂ) (g h : H) (C : G) (V : U) : ℂ :=
  tailFactor k q a T C * Ud (lowerPoint k q (g * (ι₁ h)⁻¹) V * w * (ι C)⁻¹) *
    restrictionWeight k q c.inverse (determinant (dualMatrix k q C h V))

private theorem dualFiber_eq (a : ℝˣ) (c : RealCharacterData) (F : 𝓢(Sq, ℂ))
    (T : GodementColumnFactors k q) (hF : ∀ B, F B = T.squareEval k q B) (Ud : G → ℂ)
    (g h : H) (C : G) (V : U) (X : FullLower) :
    dualFiber k q a c F T Ud g h C V X =
      rectTransform a T.leading ((ι C).val * stackRows k (q + 1) k (ι₁ h).val (shearRectangle k q h V X)) *
        dualFiberFactor k q a c T Ud g h C V := by
  let D := dualMatrix k q C h V * lowerShear k q X
  have hrow : realFourierTransform (-a)
      (realRowSchwartzFourier (k + q + 1) a (T.tail (Fin.last (q + 1))) : (I → ℝ) → ℂ) =
      T.tail (Fin.last (q + 1)) := by
    rw [← funext (realRowSchwartzFourier_apply (k + q + 1) (-a) _)]
    exact congrArg (fun f : 𝓢(I → ℝ, ℂ) => (f : (I → ℝ) → ℂ))
      (realRowSchwartzFourier_neg_comp (k + q + 1) a _)
  have hSq := realGapSplitFourier k q a F T hF D.val
  have hc (j : J) : tailColumn k q D j = tailColumn k q (ι C) j.rev := tailArgument k q C h V X j
  have hW : RealJacquet.detCharacter c.inverse.character.toMonoidHom (dualMatrix k q C h V) *
      ArchimedeanLocal.detPower realNormalizedAbs (dualMatrix k q C h V) (((k + q : ℕ) : ℂ) / 2) =
      restrictionWeight k q c.inverse (determinant (dualMatrix k q C h V)) := rfl
  unfold dualFiber paddedRestrictionKernel
  rw [hrow, hSq, lastFrequency, whittakerArgument, mul_assoc _ (RealJacquet.detCharacter _ _) _, hW]
  unfold GodementColumnFactors.squareEval fourierFactors
  change rectTransform a T.leading (leading k q D) *
      (∏ j : J, columnSchwartzFourier a (T.tail j.castSucc) (tailColumn k q D j)) *
      T.tail (Fin.last (q + 1)) (tailColumn k q C 0) *
      Ud (lowerPoint k q (g * (ι₁ h)⁻¹) V * w * (ι C)⁻¹) *
      restrictionWeight k q c.inverse (determinant (dualMatrix k q C h V)) = _
  rw [show leading k q D = _ from leadingArgument k q C h V X]
  simp only [hc, columnSchwartzFourier_apply]
  rw [tailProduct_rev]
  unfold dualFiberFactor tailFactor
  ring

/-- On the normalized chart the integrated dual test is the square transform of the leading
restriction. -/
def RealGapMatchedTestsStatement : Prop :=
  ∀ (a : ℝˣ) (c : RealCharacterData) (F : 𝓢(Sq, ℂ)) (T : GodementColumnFactors k q),
    (∀ B, F B = T.squareEval k q B) →
  ∀ (Ud : G → ℂ) (g h : H) (C : G) (V : U),
    realNormalizedAbs C.val.det = 1 →
      let μ := rectangularMeasure (realSelfDualMeasure a) (q + 1) k
      Integrable (dualFiber k q a c F T Ud g h C V) μ ∧
        (∫ X, dualFiber k q a c F T Ud g h C V X ∂μ) =
          rectFourier a (leadingRestriction k (q + 1) k C T.leading) (ι₁ h).val *
            dualFiberFactor k q a c T Ud g h C V

theorem realGapMatchedTests : RealGapMatchedTestsStatement k q := by
  intro a c F T hF Ud g h C V hdet μ
  let f (Y : FullLower) := rectTransform a T.leading ((ι C).val * stackRows k (q + 1) k (ι₁ h).val Y)
  let z := dualFiberFactor k q a c T Ud g h C V
  have hf : Integrable f μ := integrable_rectTransform_complement k (q + 1) k a C T.leading (ι₁ h).val
  have hS := measurePreserving_shearRectangle k q (realSelfDualMeasure a) h V
  have hFib : dualFiber k q a c F T Ud g h C V = fun X => (f (shearRectangle k q h V X)) * z :=
    funext (dualFiber_eq k q a c F T hF Ud g h C V)
  rw [hFib]
  refine ⟨(hS.integrable_comp_of_integrable hf).mul_const z, ?_⟩
  let e := shearRectangle k q h V
  have hMap : μ.map e = μ := hS.map_eq
  have hMeas : AEStronglyMeasurable f (μ.map e) := hMap.symm ▸ hf.aestronglyMeasurable
  have hChange : (∫ X, f (e X) ∂μ) = ∫ Y, f Y ∂μ := by
    rw [← integral_map hS.measurable.aemeasurable hMeas, hMap]
  have hLead := realGapLeadingFourier k (q + 1) k a C T.leading (ι₁ h).val
  rw [hdet, inv_one, one_pow, one_smul] at hLead
  rw [integral_mul_const]
  exact congrArg (· * z) (hChange.trans hLead.symm)

end Langlands.Global.RankinSelbergGlobal.RealGapMatchedTests
