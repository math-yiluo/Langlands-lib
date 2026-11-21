import Langlands.Global.RankinSelberg.ComplexGapOrdinarySeparation
import Langlands.Global.RankinSelberg.ComplexGapDualSeparation
import Langlands.Global.RankinSelberg.ComplexGapSquareWeighted
import Langlands.Global.RankinSelberg.ComplexUnequalWeightedTranslation

/-! # Integrating the two scaled comparisons on the normalized gap charts -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapScaleComparison

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)
open Langlands.Automorphic (complexStandardKFinite)
open Langlands.GeneralLinear (determinant inverseTranspose weylLong)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure rectangularMeasure_isAddHaar)
open Langlands.GodementJacquet (complexSelfDualMeasure_neg_scale)
open ArchimedeanLocal (ComplexQuotientMeasureData complexSelfDualMeasure complexNormalizedAbs complexUnequalIntegrand
  complexUnequalIntegral complexUnequalDualIntegral complexUnequalDualMeasure)
open ComplexAdjacentUnfolding (splitSquareTransform)
open ComplexGapAlternateRestriction (GodementColumnFactors)
open ComplexGapAlternateWeighted (leadingSide)
open ComplexGapDualChart (retainedTail)
open ComplexGapDualHaar (dualChartMeasure sigmaFinite_dualChartMeasure)
open ComplexGapDualSeparation (dualSeparatedKernel)
open ComplexGapLeadingHaar (Retained splitOuter outerWithLeading retainedTail_outerWithLeading retainedMeasure
  sigmaFinite_retainedMeasure complexGapLeadingHaar interchangeMiddle measurePreserving_interchangeMiddle
  interchangeFirst measurePreserving_interchangeFirst)
open ComplexGapOrdinarySeparation (squareLeading ordinarySeparatedKernel ordinaryChartMeasure sigmaFinite_ordinaryChartMeasure)
open ComplexGapRankCoordinates (rankLT rectangleRows measurePreserving_rectangleRows)
open ComplexGapSeparatedKernels (retainedCoefficient)
open ComplexGapSquareAverage (squareKernel)
open ComplexGapSquareReflection (leadingSquareTest)
open ComplexGapSquareWeighted (complexGapSquareWeighted)
open ComplexGapTriangularChart (Outer)
open ComplexGapUnitDeterminant (unitOuterMeasure)
open ComplexJacquet (HasComplexPairNormalizedGrowth)
open ComplexJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)
open ComplexUnequalMellinReduction (quotientDetAbs sigmaFinite_quotient)
open ComplexUnequalWeightedTranslation (complexUnequalWeightedTranslation)
open ComplexWeightedKernelReflection (ordinaryWeight reflectedWeight)
open ComplexWhittakerTranslatedIntegrals (weightedOrdinary weightedDual)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel
  archimedeanEquationComplexQMeasurable archimedeanEquationComplexQBorel

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "Q" => fun t => LeftUnipotentQuotient t ℂ
local notation "Unip" => fun n => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "KU" => fun n => unitaryCompact ℂ n
local notation "M" => fun n m => Matrix (Fin n) (Fin m) ℂ
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs
local notation "δ" => fun g => complexNormalizedAbs (Matrix.det (Units.val g))
local notation "SD" => complexSelfDualMeasure
local notation "ρ" => ArchimedeanLocal.translateFunction

variable (t q : ℕ)
local notation "Small" => t + 1
local notation "TailSize" => q + 1
local notation "UpperIndex" => t + 1 + q
local notation "Large" => t + 1 + q + 1
local notation "H" => G Small
local notation "ι" => inverseTranspose Small ℂ
local notation "ν" => complexGeneralLinearHaar Small
local notation "Tail" => Unip TailSize
local notation "Ord" => Q t × (Outer Small q × Tail)
local notation "OrdRet" => Q t × (Retained Small q × Tail)
local notation "Lower" => M q Small
local notation "NativeLower" => M (UpperIndex - Small) Small
local notation "Dual" => Q t × (Outer Small q × (Lower × Tail))
local notation "Side" => Outer Small q × Tail

private def assembleLeading (p : OrdRet × H) : Ord :=
  (p.1.1, outerWithLeading Small q p.2 p.1.2.1, p.1.2.2)

private def leadingEquiv : OrdRet × H ≃ᵐ Ord :=
  (interchangeMiddle (C := Retained Small q × Tail)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Q t))
      (MeasurableEquiv.prodAssoc.symm.trans
        (MeasurableEquiv.prodCongr (splitOuter Small q).symm (MeasurableEquiv.refl Tail))))

private theorem measurePreserving_leadingEquiv (a : ℂˣ) (D : ComplexQuotientMeasureData t)
    (κ : Measure (KU Large)) (hκ : κ.IsHaarMeasure) :
    let η := entryHaar (SD a) TailSize
    let τ := retainedMeasure Small q (SD a) κ
    MeasurePreserving (leadingEquiv t q) ((D.measure.prod (τ.prod η)).prod ν)
      (D.measure.prod (ordinaryChartMeasure t q a κ)) := by
  intro η τ
  let : κ.IsHaarMeasure := hκ
  let : SigmaFinite η := entryHaar_sigmaFinite (SD a) TailSize
  let : SigmaFinite τ := sigmaFinite_retainedMeasure Small q (SD a) κ
  let : SigmaFinite D.measure := sigmaFinite_quotient D
  have h₁ := measurePreserving_interchangeMiddle D.measure ν (τ.prod η)
  have h₂ := (measurePreserving_prodAssoc ν τ η).symm _
  have h₃ := ((complexGapLeadingHaar Small q (SD a) κ hκ).symm _).prod (MeasurePreserving.id η)
  exact ((MeasurePreserving.id D.measure).prod (h₃.comp h₂)).comp h₁

private theorem integral_over_leading (D : ComplexQuotientMeasureData t) (a : ℂˣ)
    (κ : Measure (KU Large)) (hκ : κ.IsHaarMeasure) (F : Ord → ℂ)
    (hF : Integrable F (D.measure.prod (ordinaryChartMeasure t q a κ))) :
    (∫ p, F p ∂D.measure.prod (ordinaryChartMeasure t q a κ)) =
      ∫ p : OrdRet, (∫ h : H, F (assembleLeading t q (p, h)) ∂ν)
        ∂D.measure.prod ((retainedMeasure Small q (SD a) κ).prod (entryHaar (SD a) TailSize)) := by
  let e := leadingEquiv t q
  have he := measurePreserving_leadingEquiv t q a D κ hκ
  let : κ.IsHaarMeasure := hκ
  let : SigmaFinite (retainedMeasure Small q (SD a) κ) := sigmaFinite_retainedMeasure Small q (SD a) κ
  let : SigmaFinite (entryHaar (SD a) TailSize) := entryHaar_sigmaFinite (SD a) TailSize
  let : SigmaFinite D.measure := sigmaFinite_quotient D
  have hi := he.integrable_comp_of_integrable hF
  exact (he.integral_comp e.measurableEmbedding F).symm.trans (integral_prod _ hi)

private theorem ordinarySeparatedKernel_leading (dual : Bool) (a : ℂˣ) (d : ComplexCharacterData)
    (T : GodementColumnFactors Small q) (W : G Large → ℂ) (V : H → ℂ)
    (f₁ f₂ : ℝ → ℂ) (p : OrdRet) (h : H) :
    let C := retainedTail Small q (outerWithLeading Small q 1 p.2.1) p.2.2
    let g := p.1.out
    let L := retainedCoefficient t q a d T C * weightedOrdinary (rankLT t q) (ρ C⁻¹ W) (fun _ => 1) f₁ p.1
    ordinarySeparatedKernel t q dual a d T W V f₁ f₂ (assembleLeading t q (p, h)) =
      L * (squareKernel (if dual then d.inv else d) (squareLeading t q dual a T C)
        (fun y => if dual then V (g * ι y) else V (g * y)) 0 (leadingSide dual h) * f₂ (δ (leadingSide dual h))) := by
  intro C g L
  unfold ordinarySeparatedKernel assembleLeading
  simp only [retainedTail_outerWithLeading]
  have htest : (if dual then V (g * ι (leadingSide dual h)) else V (g * leadingSide dual h)) = V (g * h) := by
    cases dual <;> simp [leadingSide, Langlands.GeneralLinear.inverseTranspose_involutive]
  unfold L weightedOrdinary complexUnequalIntegrand ArchimedeanLocal.unequalIntegrand ArchimedeanLocal.translateFunction squareKernel
  simp only [htest, mul_one]
  dsimp only [outerWithLeading, g, C]
  ring

/-- The leading square functional equation integrated over the retained variables. -/
theorem squareIntegral_reflection (D : ComplexQuotientMeasureData t) (a : ℂˣ) (κ : Measure (KU Large))
    (hκ : κ.IsHaarMeasure) (d : ComplexCharacterData) (es : List ComplexCharacterData) (hes : es.length = Small)
    (T : GodementColumnFactors Small q) (W : G Large → ℂ)
    (hT : ∀ (p : Outer Small q) (Z : Tail), FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun u : KU Small => fun X : M Small Small =>
        leadingSquareTest t q (retainedTail Small q p Z) T.leading (u.val⁻¹.val * X))))
    (B : complexStandardKFinite Small es →ₗ[ℂ] (H → ℂ)) (hB : IsComplexWhittakerIntertwiner t es a B)
    (v : complexStandardKFinite Small es) (f₁ : ℝ → ℂ) (c : ℝ) (hc : 0 < c)
    (rate L : ℝ) (hrate : 0 < rate) :
    let f₂ (x : ℝ) := ordinaryWeight [d] es a 1 rate L (c * x)
    let k₂ (x : ℝ) := reflectedWeight [d] es rate L (c⁻¹ * x)
    let m₀ := D.measure.prod (ordinaryChartMeasure t q a κ)
    let F := ordinarySeparatedKernel t q false a d T W (B v) f₁ f₂
    let Fm := ordinarySeparatedKernel t q true a d T W (B v) f₁ k₂
    Integrable F m₀ → Integrable Fm m₀ → (∫ p, F p ∂m₀) = (c : ℂ) * ∫ p, Fm p ∂m₀ := by
  intro f₂ k₂ m₀ F Fm hF hFm
  have h₁ := integral_over_leading t q D a κ hκ F hF
  have h₂ := integral_over_leading t q D a κ hκ Fm hFm
  rw [h₁, h₂, ← integral_const_mul]
  apply integral_congr_ae
  refine ae_of_all _ fun p => ?_
  let C := retainedTail Small q (outerWithLeading Small q 1 p.2.1) p.2.2
  let g := p.1.out
  let Φ := leadingSquareTest t q C T.leading
  let L₀ := retainedCoefficient t q a d T C * weightedOrdinary (rankLT t q) (ρ C⁻¹ W) (fun _ => 1) f₁ p.1
  have hEq := complexGapSquareWeighted t a d es hes Φ (hT _ _) B hB v g rate L hrate c hc
  dsimp only [F, Fm]
  simp_rw [ordinarySeparatedKernel_leading]
  simp only [Bool.false_eq_true, ↓reduceIte, leadingSide, squareLeading]
  rw [integral_const_mul, integral_const_mul]
  change L₀ * (∫ y : H, squareKernel d Φ (fun z => B v (g * z)) 0 y * f₂ (δ y) ∂ν) =
    (c : ℂ) * (L₀ * (∫ y : H, squareKernel d.inv (splitSquareTransform a Φ)
      (fun z => B v (g * ι z)) 0 (ι y) * k₂ (δ (ι y)) ∂ν))
  have hRev (y : H) : squareKernel d.inv (splitSquareTransform a Φ) (fun z => B v (g * ι z)) 0 (ι y) =
      squareKernel d.inv (splitSquareTransform a Φ) (fun _ => 1) 0 (ι y) * B v (g * y) := by
    simp only [squareKernel, mul_one, Langlands.GeneralLinear.inverseTranspose_involutive]
  simp_rw [hRev]
  rw [show (∫ y : H, squareKernel d Φ (fun z => B v (g * z)) 0 y * f₂ (δ y) ∂ν) = _ from hEq]
  ring

private def assembleLower (p : Side × (Q t × NativeLower)) : Dual :=
  (p.2.1, p.1.1, rectangleRows t q p.2.2, p.1.2)

private def lowerEquiv : Side × (Q t × NativeLower) ≃ᵐ Dual :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Side)
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Q t)) (rectangleRows t q))).trans
    (MeasurableEquiv.prodComm.trans (MeasurableEquiv.prodAssoc.trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Q t)) interchangeFirst)))

private theorem measurePreserving_lowerEquiv (D : ComplexQuotientMeasureData t) (a : ℂˣ)
    (κ : Measure (KU Large)) (hκ : κ.IsHaarMeasure) :
    MeasurePreserving (lowerEquiv t q)
      ((ordinaryChartMeasure t q a κ).prod (complexUnequalDualMeasure (r := UpperIndex) (-a) D))
      (D.measure.prod (dualChartMeasure t q a κ)) := by
  let σ := unitOuterMeasure Small q (SD a) κ
  let η := entryHaar (SD a) TailSize
  let ξ := rectangularMeasure (SD a) q Small
  let ξ₀ := rectangularMeasure (SD a) (UpperIndex - Small) Small
  let : κ.IsHaarMeasure := hκ
  let : CompactSpace (KU Large) := Langlands.Archimedean.ComplexDuality.compactSpace_unitaryCompact _
  let : (SD a).measure.IsAddHaarMeasure := (SD a).isAddHaar
  let : SigmaFinite (SD a).measure := inferInstance
  let : SigmaFinite (ComplexGapTriangularChart.outerMeasure Small q (SD a) κ) := by
    unfold ComplexGapTriangularChart.outerMeasure
    infer_instance
  let : SigmaFinite σ := SigmaFinite.withDensity _
  let : SigmaFinite η := entryHaar_sigmaFinite (SD a) TailSize
  let : SigmaFinite D.measure := sigmaFinite_quotient D
  let : ξ.IsAddHaarMeasure := rectangularMeasure_isAddHaar _ _ _
  let : ξ₀.IsAddHaarMeasure := rectangularMeasure_isAddHaar _ _ _
  let : SigmaFinite ξ := inferInstance
  let : SigmaFinite ξ₀ := inferInstance
  have hμ : complexUnequalDualMeasure (r := UpperIndex) (-a) D = D.measure.prod ξ₀ := by
    unfold complexUnequalDualMeasure
    rw [complexSelfDualMeasure_neg_scale]
  rw [hμ]
  have h₁ := (MeasurePreserving.id (σ.prod η)).prod
    ((MeasurePreserving.id D.measure).prod (measurePreserving_rectangleRows t q (SD a)))
  have h₂ : MeasurePreserving Prod.swap ((σ.prod η).prod (D.measure.prod ξ)) ((D.measure.prod ξ).prod (σ.prod η)) :=
    measurePreserving_swap
  have h₃ := measurePreserving_prodAssoc D.measure ξ (σ.prod η)
  have h₄ := (MeasurePreserving.id D.measure).prod (measurePreserving_interchangeFirst ξ σ η)
  exact h₄.comp (h₃.comp (h₂.comp h₁))

private theorem integral_over_lower (D : ComplexQuotientMeasureData t) (a : ℂˣ) (κ : Measure (KU Large))
    (hκ : κ.IsHaarMeasure) (F : Dual → ℂ) (hF : Integrable F (D.measure.prod (dualChartMeasure t q a κ))) :
    (∫ p, F p ∂D.measure.prod (dualChartMeasure t q a κ)) =
      ∫ p : Side, (∫ u, F (assembleLower t q (p, u)) ∂complexUnequalDualMeasure (r := UpperIndex) (-a) D)
        ∂ordinaryChartMeasure t q a κ := by
  let e := lowerEquiv t q
  have he := measurePreserving_lowerEquiv t q D a κ hκ
  let : κ.IsHaarMeasure := hκ
  let : SigmaFinite (ordinaryChartMeasure t q a κ) := sigmaFinite_ordinaryChartMeasure t q a κ
  let : SigmaFinite D.measure := sigmaFinite_quotient D
  let : (rectangularMeasure (SD (-a)) (UpperIndex - Small) Small).IsAddHaarMeasure :=
    rectangularMeasure_isAddHaar _ _ _
  let : SigmaFinite (complexUnequalDualMeasure (r := UpperIndex) (-a) D) := by
    unfold complexUnequalDualMeasure
    infer_instance
  have hi := he.integrable_comp_of_integrable hF
  exact (he.integral_comp e.measurableEmbedding F).symm.trans (integral_prod _ hi)

/-- The smaller unequal functional equation integrated at every retained and leading matrix. -/
theorem lowerIntegral_reflection (D : ComplexQuotientMeasureData t) (a : ℂˣ) (κ : Measure (KU Large))
    (hκ : κ.IsHaarMeasure) (d : ComplexCharacterData) (ds es : List ComplexCharacterData)
    (T : GodementColumnFactors Small q)
    (hN : ∀ (W : complexWhittakerModel UpperIndex ds (-a)) (V : complexWhittakerModel t es a),
      HasComplexPairNormalizedGrowth ds es (-a) (complexCentralSign es ^ UpperIndex)
        (complexUnequalIntegral (rankLT t q) D W.val V.val)
        (complexUnequalDualIntegral (rankLT t q) (-a) D W.val V.val))
    (B : complexStandardKFinite Large ds →ₗ[ℂ] (G Large → ℂ)) (hB : IsComplexWhittakerIntertwiner UpperIndex ds (-a) B)
    (B' : complexStandardKFinite Small es →ₗ[ℂ] (H → ℂ)) (hB' : IsComplexWhittakerIntertwiner t es a B')
    (v : complexStandardKFinite Large ds) (v' : complexStandardKFinite Small es)
    (k₂ : ℝ → ℂ) (b : ℝ) (hb : 0 < b) (rate L : ℝ) (hrate : 0 < rate) :
    let f₁ (x : ℝ) := ordinaryWeight ds es (-a) (complexCentralSign es ^ UpperIndex) rate L (b * x)
    let k₁ (x : ℝ) := reflectedWeight ds es rate L (b⁻¹ * x)
    let m₀ := D.measure.prod (ordinaryChartMeasure t q a κ)
    let md := D.measure.prod (dualChartMeasure t q a κ)
    let Fm := ordinarySeparatedKernel t q true a d T (B v) (B' v') f₁ k₂
    let Fd := dualSeparatedKernel t q a d T (B v) (B' v') k₁ k₂
    Integrable Fm m₀ → Integrable Fd md →
      (d.inv.character (determinant (weylLong TailSize ℂ)) : ℂ) * (∫ p, Fm p ∂m₀) =
        (b : ℂ) * ∫ p, Fd p ∂md := by
  intro f₁ k₁ m₀ md Fm Fd hFm hFd
  let S := (d.inv.character (determinant (weylLong TailSize ℂ)) : ℂ)
  let : κ.IsHaarMeasure := hκ
  let : SigmaFinite D.measure := sigmaFinite_quotient D
  let : SigmaFinite (ordinaryChartMeasure t q a κ) := sigmaFinite_ordinaryChartMeasure t q a κ
  have hd := integral_over_lower t q D a κ hκ Fd hFd
  have hm := integral_prod_symm Fm hFm
  rw [hm, hd, ← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  refine ae_of_all _ fun p => ?_
  let z := p.1.1.1.1
  let C := retainedTail Small q p.1 p.2
  let Φ := leadingSquareTest t q C T.leading
  let L₀ := retainedCoefficient t q a d T C *
    squareKernel d.inv (splitSquareTransform a Φ) (fun _ => 1) 0 (ι z) * k₂ (δ (ι z))
  let W := ρ C⁻¹ (B v)
  let V := ρ z (B' v')
  have hNB (U : complexWhittakerModel UpperIndex ds (-a)) (V₀ : complexWhittakerModel t es (-(-a))) :
      HasComplexPairNormalizedGrowth ds es (-a) (complexCentralSign es ^ UpperIndex)
        (complexUnequalIntegral (rankLT t q) D U.val V₀.val)
        (complexUnequalDualIntegral (rankLT t q) (-a) D U.val V₀.val) :=
    hN U ⟨V₀.val, by simpa only [neg_neg] using V₀.2⟩
  have hB'' : IsComplexWhittakerIntertwiner t es (-(-a)) B' := by simpa only [neg_neg] using hB'
  have hL := (complexUnequalWeightedTranslation UpperIndex t (rankLT t q) ds es (-a) D hNB
    B B' hB hB'' v v' C⁻¹ z rate L hrate hb).2.2
  have hscale (u : Q t × NativeLower) : weightedDual (rankLT t q) W V (fun x => (b : ℂ) * k₁ x) u =
      (b : ℂ) * weightedDual (rankLT t q) W V k₁ u := by unfold weightedDual; ring
  change (∫ x, weightedOrdinary (rankLT t q) W V f₁ x ∂D.measure) =
    ∫ y, weightedDual (rankLT t q) W V (fun x => (b : ℂ) * k₁ x) y
      ∂complexUnequalDualMeasure (r := UpperIndex) (-a) D at hL
  simp_rw [hscale, integral_const_mul] at hL
  have hmF (x : Q t) : Fm (x, p) = L₀ * weightedOrdinary (rankLT t q) W V f₁ x := by
    unfold Fm ordinarySeparatedKernel
    simp only [leadingSide, squareLeading, ite_true]
    dsimp only [L₀, Φ, W, V, C, z]
    ring
  have hdF (u : Q t × NativeLower) : Fd (assembleLower t q (p, u)) =
      (S * L₀) * weightedDual (rankLT t q) W V k₁ u := by
    unfold Fd assembleLower dualSeparatedKernel
    simp only [MeasurableEquiv.symm_apply_apply]
    change _ = _ * weightedDual (rankLT t q) W V k₁ (u.1, u.2)
    dsimp only [S, L₀, Φ, W, V, C, z]
    ring
  change S * (∫ x : Q t, Fm (x, p) ∂D.measure) =
    (b : ℂ) * (∫ u, Fd (assembleLower t q (p, u)) ∂complexUnequalDualMeasure (r := UpperIndex) (-a) D)
  simp_rw [hmF, hdF, integral_const_mul]
  rw [hL]
  ring

/-- The two scaled comparisons compose with the explicit tail Weyl scalar. -/
def ComplexGapScaleComparisonStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData t) (a : ℂˣ) (κ : Measure (KU Large)), κ.IsHaarMeasure →
    ∀ (d : ComplexCharacterData) (ds es : List ComplexCharacterData), es.length = Small →
    ∀ (T : GodementColumnFactors Small q),
    (∀ (p : Outer Small q) (Z : Tail), FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun u : KU Small => fun X : M Small Small =>
        leadingSquareTest t q (retainedTail Small q p Z) T.leading (u.val⁻¹.val * X)))) →
    (∀ (W : complexWhittakerModel UpperIndex ds (-a)) (V : complexWhittakerModel t es a),
      HasComplexPairNormalizedGrowth ds es (-a) (complexCentralSign es ^ UpperIndex)
        (complexUnequalIntegral (rankLT t q) D W.val V.val)
        (complexUnequalDualIntegral (rankLT t q) (-a) D W.val V.val)) →
    ∀ (B : complexStandardKFinite Large ds →ₗ[ℂ] (G Large → ℂ)),
      IsComplexWhittakerIntertwiner UpperIndex ds (-a) B →
    ∀ (B' : complexStandardKFinite Small es →ₗ[ℂ] (H → ℂ)),
      IsComplexWhittakerIntertwiner t es a B' →
    ∀ (v : complexStandardKFinite Large ds) (v' : complexStandardKFinite Small es)
      (b c : ℝ), 0 < b → 0 < c →
    ∀ (rate L : ℝ), 0 < rate →
      let f₁ (x : ℝ) := ordinaryWeight ds es (-a) (complexCentralSign es ^ UpperIndex) rate L (b * x)
      let f₂ (x : ℝ) := ordinaryWeight [d] es a 1 rate L (c * x)
      let k₁ (x : ℝ) := reflectedWeight ds es rate L (b⁻¹ * x)
      let k₂ (x : ℝ) := reflectedWeight [d] es rate L (c⁻¹ * x)
      let m₀ := D.measure.prod (ordinaryChartMeasure t q a κ)
      let md := D.measure.prod (dualChartMeasure t q a κ)
      let F := ordinarySeparatedKernel t q false a d T (B v) (B' v') f₁ f₂
      let Fm := ordinarySeparatedKernel t q true a d T (B v) (B' v') f₁ k₂
      let Fd := dualSeparatedKernel t q a d T (B v) (B' v') k₁ k₂
      Integrable F m₀ → Integrable Fm m₀ → Integrable Fd md →
        (d.inv.character (determinant (weylLong TailSize ℂ)) : ℂ) * (∫ p, F p ∂m₀) =
          ((b * c : ℝ) : ℂ) * ∫ p, Fd p ∂md

theorem complexGapScaleComparison : ComplexGapScaleComparisonStatement t q := by
  intro D a κ hκ d ds es hes T hT hN B hB B' hB' v v' b c hb hc rate L hrate
    f₁ f₂ k₁ k₂ m₀ md F Fm Fd hF hFm hFd
  let S := (d.inv.character (determinant (weylLong TailSize ℂ)) : ℂ)
  have hs : (∫ p, F p ∂m₀) = (c : ℂ) * ∫ p, Fm p ∂m₀ :=
    squareIntegral_reflection t q D a κ hκ d es hes T (B v) hT B' hB' v' f₁ c hc rate L hrate hF hFm
  have hl : S * (∫ p, Fm p ∂m₀) = (b : ℂ) * ∫ p, Fd p ∂md :=
    lowerIntegral_reflection t q D a κ hκ d ds es T hN B hB B' hB' v v' k₂ b hb rate L hrate hFm hFd
  change S * (∫ p, F p ∂m₀) = _
  rw [hs, mul_left_comm S, hl, Complex.ofReal_mul]
  ring

end Langlands.Global.RankinSelbergGlobal.ComplexGapScaleComparison
