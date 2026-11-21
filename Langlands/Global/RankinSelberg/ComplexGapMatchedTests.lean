import Langlands.Global.RankinSelberg.ComplexGapDualArguments
import Langlands.Global.RankinSelberg.ComplexGapSplitFourier

/-! # Matching the split tests in the two Godement integrals -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapMatchedTests

open Langlands.GeneralLinear (rankInclusion inverseTranspose determinant)
open Langlands.GodementJacquet (complexSelfDualMeasure_neg_scale)
open Langlands.HarmonicAnalysis (rectangularJoin)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.RankinSelberg (rectangularMeasure)
open ArchimedeanLocal (complexSelfDualMeasure complexNormalizedAbs)
open ComplexGapAlternateRestriction (GodementColumnFactors restrictionWeight partial_join)
open ComplexGapDualArguments (leading tailColumn dualMatrix lowerPoint shearRectangle
  leadingArgument tailArgument lastFrequency whittakerArgument measurePreserving_shearRectangle)
open ComplexGapDualChart (lowerShear)
open ComplexGapLeadingFourier (leadingRestriction leadingRestriction_apply stackRows rectTransform
  complexGapLeadingFourier integrable_rectTransform_complement)
open ComplexGapSplitFourier (fourierFactors columnTransform columnTransform_apply complexGapSplitFourier fourier_columnTransform_neg)
open ComplexGodementFourier (rectFourier)
open ComplexGapTailExchange (alternateBlockTailKernel fixedTailFactor)
open ComplexGapUpperTail (packedTail)
open ComplexGapWeylRestriction (reverseTail tailWeyl)
open ComplexGodementPaddedRestriction (paddedRestrictionKernel)

variable (k q : ℕ)
local notation "I" => Fin (k + q + 1)
local notation "J" => Fin (q + 1)
local notation "G" => Langlands.GeneralLinear (k + q + 1) ℂ
local notation "H" => Langlands.GeneralLinear k ℂ
local notation "A" => rankInclusion (R := ℂ) (n := k) (q + 1)
local notation "ι" => inverseTranspose (k + q + 1) ℂ
local notation "ι₁" => inverseTranspose k ℂ
local notation "w" => tailWeyl k (q + 1)
local notation "Rect" => Matrix I (Fin (k + q + 2)) ℂ
local notation "U" => Matrix (Fin q) (Fin k) ℂ
local notation "FullLower" => Matrix J (Fin k) ℂ
local notation "row" => Langlands.RankinSelberg.lastRow
local notation "Fcol" => ComplexGodementFourier.fourier

/-- The shared tail contribution after matching the rotated ordinary test and the dual test. -/
def tailFactor (a : ℂˣ) (T : GodementColumnFactors k q) (C : G) : ℂ :=
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
theorem tailFactor_reverse (a : ℂˣ) (T : GodementColumnFactors k q) (C : G) :
    tailFactor k q a T C =
      T.tail (Fin.last (q + 1)) (tailColumn k q C 0) *
        Fcol a (T.tail 0) (row C⁻¹) *
          ∏ j : Fin q, Fcol a (T.tail j.succ.castSucc.rev) (tailColumn k q (ι C) j.castSucc) := by
  unfold tailFactor
  rw [Fin.prod_univ_castSucc]
  simp only [rev_index, Fin.rev_last, Fin.castSucc_zero, ← lastFrequency_inverseTranspose]
  ring

/-- The split ordinary kernel after rotation has the shared tail factor. -/
theorem alternateBlockTailKernel_reverse (a : ℂˣ) (T : GodementColumnFactors k q) (W : G → ℂ)
    (χ : ℂˣ →* ℂ) (g h : H) (B : G) (Z : Langlands.GeneralLinear.upperUnipotent (q + 1) ℂ) :
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

private theorem tailProduct_rev (a : ℂˣ) (T : GodementColumnFactors k q) (C : G) :
    (∏ j : J, Fcol a (T.tail j.castSucc) (tailColumn k q (ι C) j.rev)) =
      ∏ j : J, Fcol a (T.tail j.rev.castSucc) (tailColumn k q (ι C) j) := by
  refine Fintype.prod_equiv (Fin.revPerm : Equiv.Perm J) _ _ ?_
  intro j
  change Fcol a (T.tail j.castSucc) _ = Fcol a (T.tail j.rev.rev.castSucc) _
  rw [Fin.rev_rev]
  rfl

private theorem split_dual_partial (a : ℂˣ) (Φ : 𝓢(Rect, ℂ)) (T : GodementColumnFactors k q)
    (hT : ∀ X, Φ X = T.eval k q X) (C : G) (g h : H) (V : U) (X : FullLower) :
    ComplexGodementPartialFourier.partialSchwartz (-a) (complexSelfDualMeasure a) (rectTransform a Φ)
      (rectangularJoin (dualMatrix k q C h V * lowerShear k q X).val (row (A g * (dualMatrix k q C h V)⁻¹))) =
      rectTransform a T.leading ((ι C).val * stackRows k (q + 1) k (ι₁ h).val (shearRectangle k q h V X)) *
        tailFactor k q a T C := by
  let D := dualMatrix k q C h V * lowerShear k q X
  let v := row (A g * (dualMatrix k q C h V)⁻¹)
  let Td := fourierFactors k q a T
  have hμ : complexSelfDualMeasure (-a) = complexSelfDualMeasure a := complexSelfDualMeasure_neg_scale a
  have hPartial := partial_join k q (-a) (rectTransform a Φ) Td (complexGapSplitFourier k q a Φ T hT) D.val v
  rw [hμ] at hPartial
  refine hPartial.trans ?_
  change (rectTransform a T.leading (leading k q D) * Td.tail 0 (tailColumn k q D 0) *
    ∏ j : Fin q, Td.tail j.succ.castSucc (tailColumn k q D j.succ)) *
      Fcol (-a) (columnTransform a (T.tail (Fin.last (q + 1)))) v = _
  rw [fourier_columnTransform_neg, show v = tailColumn k q C 0 from lastFrequency k q C g h V,
    show leading k q D = _ from leadingArgument k q C h V X]
  have hc (j : J) : tailColumn k q D j = tailColumn k q (ι C) j.rev := tailArgument k q C h V X j
  simp only [hc, Td, fourierFactors, columnTransform_apply]
  have hProd := Fin.prod_univ_succ (f := fun j : J => Fcol a (T.tail j.castSucc) (tailColumn k q (ι C) j.rev))
  simp only [Fin.castSucc_zero] at hProd
  rw [mul_assoc (rectTransform a T.leading _), ← hProd, tailProduct_rev]
  unfold tailFactor
  ring

/-- Exact dual integrand before integration in its complementary rectangle. -/
def dualFiber (a : ℂˣ) (d : ComplexCharacterData) (Φ : 𝓢(Rect, ℂ)) (Wd : G → ℂ)
    (g h : H) (C : G) (V : U) (s : ℂ) (X : FullLower) : ℂ :=
  paddedRestrictionKernel (complexSelfDualMeasure a) d.inv (-a) (rectTransform a Φ) Wd
    (A g) (lowerShear k q X) (-s) (dualMatrix k q C h V)

/-- The factor independent of the complementary rectangle in the dual integral. -/
def dualFiberFactor (a : ℂˣ) (d : ComplexCharacterData) (T : GodementColumnFactors k q)
    (Wd : G → ℂ) (g h : H) (C : G) (V : U) (s : ℂ) : ℂ :=
  tailFactor k q a T C * Wd (lowerPoint k q (g * (ι₁ h)⁻¹) V * w * (ι C)⁻¹) *
    restrictionWeight k q d.inv (-s) (determinant (dualMatrix k q C h V))

private theorem dualFiber_eq (a : ℂˣ) (d : ComplexCharacterData) (Φ : 𝓢(Rect, ℂ))
    (T : GodementColumnFactors k q) (hT : ∀ X, Φ X = T.eval k q X) (Wd : G → ℂ)
    (g h : H) (C : G) (V : U) (s : ℂ) (X : FullLower) :
    dualFiber k q a d Φ Wd g h C V s X =
      rectTransform a T.leading ((ι C).val * stackRows k (q + 1) k (ι₁ h).val (shearRectangle k q h V X)) *
        dualFiberFactor k q a d T Wd g h C V s := by
  unfold dualFiber paddedRestrictionKernel
  change ComplexGodementPartialFourier.partialSchwartz (-a) (complexSelfDualMeasure a) (rectTransform a Φ)
    (rectangularJoin (dualMatrix k q C h V * lowerShear k q X).val (row (A g * (dualMatrix k q C h V)⁻¹))) *
      Wd (A g * (dualMatrix k q C h V)⁻¹) * restrictionWeight k q d.inv (-s) (determinant (dualMatrix k q C h V)) = _
  rw [split_dual_partial k q a Φ T hT, whittakerArgument]
  simp only [dualFiberFactor, mul_assoc]

/-- On the normalized chart the integrated dual test is the positive square transform of the leading restriction. -/
def ComplexGapMatchedTestsStatement : Prop :=
  ∀ (a : ℂˣ) (d : ComplexCharacterData) (Φ : 𝓢(Rect, ℂ)) (T : GodementColumnFactors k q),
    (∀ X, Φ X = T.eval k q X) →
  ∀ (Wd : G → ℂ) (g h : H) (C : G) (V : U) (s : ℂ),
    complexNormalizedAbs C.val.det = 1 →
      let μ := rectangularMeasure (complexSelfDualMeasure a) (q + 1) k
      Integrable (dualFiber k q a d Φ Wd g h C V s) μ ∧
        (∫ X, dualFiber k q a d Φ Wd g h C V s X ∂μ) =
          rectFourier a (leadingRestriction k (q + 1) k C T.leading) (ι₁ h).val *
            dualFiberFactor k q a d T Wd g h C V s

theorem complexGapMatchedTests : ComplexGapMatchedTestsStatement k q := by
  intro a d Φ T hT Wd g h C V s hdet μ
  let f (Y : FullLower) := rectTransform a T.leading ((ι C).val * stackRows k (q + 1) k (ι₁ h).val Y)
  let z := dualFiberFactor k q a d T Wd g h C V s
  have hf : Integrable f μ := integrable_rectTransform_complement k (q + 1) k a C T.leading (ι₁ h).val
  have hS := measurePreserving_shearRectangle k q (complexSelfDualMeasure a) h V
  have hF : dualFiber k q a d Φ Wd g h C V s = fun X => (f (shearRectangle k q h V X)) * z :=
    funext (dualFiber_eq k q a d Φ T hT Wd g h C V s)
  rw [hF]
  refine ⟨(hS.integrable_comp_of_integrable hf).mul_const z, ?_⟩
  let e := shearRectangle k q h V
  have hMap : μ.map e = μ := hS.map_eq
  have hMeas : AEStronglyMeasurable f (μ.map e) := hMap.symm ▸ hf.aestronglyMeasurable
  have hChange : (∫ X, f (e X) ∂μ) = ∫ Y, f Y ∂μ := by
    rw [← integral_map hS.measurable.aemeasurable hMeas, hMap]
  have hLead := complexGapLeadingFourier k (q + 1) k a C T.leading (ι₁ h).val
  rw [hdet, inv_one, one_pow, one_smul] at hLead
  rw [integral_mul_const]
  exact congrArg (· * z) (hChange.trans hLead.symm)

end Langlands.Global.RankinSelbergGlobal.ComplexGapMatchedTests
