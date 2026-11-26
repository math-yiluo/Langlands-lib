import Langlands.Global.RankinSelberg.RealGapOrdinarySeparation
import Langlands.Global.RankinSelberg.RealGapDualSeparation
import Langlands.Global.RankinSelberg.RealGapSquareWeighted
import Langlands.Global.RankinSelberg.RealUnequalWeightedTranslation
import Langlands.Global.RankinSelberg.RealJacquetConventionReduction

/-! # Integrating the two scaled comparisons on the normalized real gap charts -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped Matrix.Norms.Operator SchwartzMap NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGapScaleComparison

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (determinant inverseTranspose weylLong)
open Langlands.LocalFactor.Archimedean (RealBlock RealCharacterData)
open Langlands.QuotientIntegration (leftQuotient_isOpenQuotientMap)
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure rectangularMeasure_isAddHaar)
open ArchimedeanLocal (RealQuotientMeasureData realSelfDualMeasure realNormalizedAbs realUnequalIntegrand
  realUnequalIntegral realUnequalDualIntegral realUnequalDualMeasure)
open RealJacquet (realAdjacentMatrixWeight detCharacter HasRealPairNormalizedGrowth)
open RealGapAlternateRestriction (GodementColumnFactors)
open RealGapAlternateWeighted (leadingSide)
open RealGapDualChart (retainedTail)
open RealGapDualHaar (dualChartMeasure sigmaFinite_dualChartMeasure)
open RealGapDualSeparation (dualSeparatedKernel)
open RealGapLeadingFourier (leadingRestriction)
open RealGapLeadingHaar (Retained splitOuter outerWithLeading retainedTail_outerWithLeading retainedMeasure
  sigmaFinite_retainedMeasure realGapLeadingHaar interchangeMiddle measurePreserving_interchangeMiddle
  interchangeFirst measurePreserving_interchangeFirst)
open RealGapOrdinarySeparation (squareLeading sideCharacter ordinarySeparatedKernel ordinaryChartMeasure
  sigmaFinite_ordinaryChartMeasure)
open RealGapRankCoordinates (rankLT rectangleRows measurePreserving_rectangleRows)
open RealGapSeparatedKernels (retainedCoefficient)
open RealGapSquareWeighted (realGapSquareWeighted)
open RealGapTriangularChart (Outer)
open RealGapUnitDeterminant (unitOuterMeasure)
open RealGodement (realRectangularSchwartzFourier)
open RealJacquetUnipotentMeasure (entryHaar entryHaar_sigmaFinite)
open RealUnequalMellinReduction (quotientDetAbs sigmaFinite_quotient)
open RealUnequalWeightedTranslation (realUnequalWeightedTranslation)
open RealWeightedKernelReflection (ordinaryWeight reflectedWeight)
open RealWhittakerTranslatedIntegrals (weightedOrdinary weightedDual)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "Q" => fun t => LeftUnipotentQuotient t ℝ
local notation "Unip" => fun n => Langlands.GeneralLinear.upperUnipotent n ℝ
local notation "KU" => fun n => unitaryCompact ℝ n
local notation "M" => fun n m => Matrix (Fin n) (Fin m) ℝ
local notation "P" => ArchimedeanLocal.detPower realNormalizedAbs
local notation "δ" => fun g => realNormalizedAbs (Matrix.det (Units.val g))
local notation "SD" => realSelfDualMeasure
local notation "ρ" => ArchimedeanLocal.translateFunction
local notation "Std" => Langlands.Automorphic.realStandardKFinite

local instance gapScaleGLMeasurable (n : ℕ) : MeasurableSpace (G n) := borel _
local instance gapScaleGLBorel (n : ℕ) : BorelSpace (G n) := ⟨rfl⟩
local instance gapScaleGLSecondCountable (n : ℕ) : SecondCountableTopology (G n) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) n).isInducing.secondCountableTopology
local instance gapScaleGLLocallyCompact (n : ℕ) : LocallyCompactSpace (G n) :=
  (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℝ) n).locallyCompactSpace
local instance gapScaleUMeasurable (n : ℕ) : MeasurableSpace (Unip n) := borel _
local instance gapScaleUBorel (n : ℕ) : BorelSpace (Unip n) := ⟨rfl⟩
local instance gapScaleQMeasurable (n : ℕ) : MeasurableSpace (Q n) := borel _
local instance gapScaleQBorel (n : ℕ) : BorelSpace (Q n) := ⟨rfl⟩

variable (t q : ℕ)
local notation "Small" => t + 1
local notation "TailSize" => q + 1
local notation "UpperIndex" => t + 1 + q
local notation "Large" => t + 1 + q + 1
local notation "H" => G Small
local notation "ι" => inverseTranspose Small ℝ
local notation "Tail" => Unip TailSize
local notation "Ord" => Q t × (Outer Small q × Tail)
local notation "OrdRet" => Q t × (Retained Small q × Tail)
local notation "Lower" => M q Small
local notation "NativeLower" => M (UpperIndex - Small) Small
local notation "Dual" => Q t × (Outer Small q × (Lower × Tail))
local notation "Side" => Outer Small q × Tail
local notation "O" => Matrix.unitaryGroup (Fin (t + 1)) ℝ

private def assembleLeading (p : OrdRet × H) : Ord :=
  (p.1.1, outerWithLeading Small q p.2 p.1.2.1, p.1.2.2)

private def leadingEquiv : OrdRet × H ≃ᵐ Ord :=
  (interchangeMiddle (C := Retained Small q × Tail)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Q t))
      (MeasurableEquiv.prodAssoc.symm.trans
        (MeasurableEquiv.prodCongr (splitOuter Small q).symm (MeasurableEquiv.refl Tail))))

private theorem measurePreserving_leadingEquiv (a : ℝˣ) (D : RealQuotientMeasureData t)
    (η₁ : Measure H) (κ : Measure (KU Large)) (hη₁ : η₁.IsHaarMeasure) (hκ : κ.IsHaarMeasure) :
    let η := entryHaar (SD a) TailSize
    let τ := retainedMeasure Small q (SD a) κ
    MeasurePreserving (leadingEquiv t q) ((D.measure.prod (τ.prod η)).prod η₁)
      (D.measure.prod (ordinaryChartMeasure t q a η₁ κ)) := by
  intro η τ
  let : κ.IsHaarMeasure := hκ
  let : η₁.IsHaarMeasure := hη₁
  let : SigmaFinite η := entryHaar_sigmaFinite (SD a) TailSize
  let : SigmaFinite τ := sigmaFinite_retainedMeasure Small q (SD a) κ
  let : SigmaFinite D.measure := sigmaFinite_quotient D
  have h₁ := measurePreserving_interchangeMiddle D.measure η₁ (τ.prod η)
  have h₂ := (measurePreserving_prodAssoc η₁ τ η).symm _
  have h₃ := ((realGapLeadingHaar Small q (SD a) η₁ κ hη₁ hκ).symm _).prod (MeasurePreserving.id η)
  exact ((MeasurePreserving.id D.measure).prod (h₃.comp h₂)).comp h₁

private theorem integral_over_leading (D : RealQuotientMeasureData t) (a : ℝˣ) (η₁ : Measure H)
    (κ : Measure (KU Large)) (hη₁ : η₁.IsHaarMeasure) (hκ : κ.IsHaarMeasure) (F : Ord → ℂ)
    (hF : Integrable F (D.measure.prod (ordinaryChartMeasure t q a η₁ κ))) :
    (∫ p, F p ∂D.measure.prod (ordinaryChartMeasure t q a η₁ κ)) =
      ∫ p : OrdRet, (∫ h : H, F (assembleLeading t q (p, h)) ∂η₁)
        ∂D.measure.prod ((retainedMeasure Small q (SD a) κ).prod (entryHaar (SD a) TailSize)) := by
  let e := leadingEquiv t q
  have he := measurePreserving_leadingEquiv t q a D η₁ κ hη₁ hκ
  let : κ.IsHaarMeasure := hκ
  let : η₁.IsHaarMeasure := hη₁
  let : SigmaFinite (retainedMeasure Small q (SD a) κ) := sigmaFinite_retainedMeasure Small q (SD a) κ
  let : SigmaFinite (entryHaar (SD a) TailSize) := entryHaar_sigmaFinite (SD a) TailSize
  let : SigmaFinite D.measure := sigmaFinite_quotient D
  have hi := he.integrable_comp_of_integrable hF
  exact (he.integral_comp e.measurableEmbedding F).symm.trans (integral_prod _ hi)

private theorem ordinarySeparatedKernel_leading (dual : Bool) (a : ℝˣ) (c : RealCharacterData)
    (T : GodementColumnFactors Small q) (W : G Large → ℂ) (V : H → ℂ)
    (f₁ f₂ : ℝ → ℂ) (p : OrdRet) (h : H) :
    let C := retainedTail Small q (outerWithLeading Small q 1 p.2.1) p.2.2
    let g := p.1.out
    let L := retainedCoefficient t q a c T C * weightedOrdinary (rankLT t q) (ρ C⁻¹ W) (fun _ => 1) f₁ p.1
    ordinarySeparatedKernel t q dual a c T W V f₁ f₂ (assembleLeading t q (p, h)) =
      L * (realAdjacentMatrixWeight (sideCharacter dual c).character.toMonoidHom
        (squareLeading t q dual a T C) 0 (leadingSide dual h) * V (g * h) * f₂ (δ (leadingSide dual h))) := by
  intro C g L
  unfold ordinarySeparatedKernel assembleLeading
  simp only [retainedTail_outerWithLeading]
  unfold L weightedOrdinary realUnequalIntegrand ArchimedeanLocal.unequalIntegrand
    ArchimedeanLocal.translateFunction
  simp only [mul_one]
  dsimp only [outerWithLeading, g, C]
  ring

/-- The leading square functional equation integrated over the retained variables. -/
theorem squareIntegral_reflection (D : RealQuotientMeasureData t) (a : ℝˣ) (κ : Measure (KU Large))
    (hκ : κ.IsHaarMeasure) (c : RealCharacterData) (fs : List RealCharacterData)
    (hfs : fs.length = Small) (T : GodementColumnFactors Small q) (W : G Large → ℂ)
    (hT : ∀ (p : Outer Small q) (Z : Tail), FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun u : O => fun X : M Small Small =>
        leadingRestriction Small TailSize Small (retainedTail Small q p Z) T.leading
          ((((Unitary.toUnits u : H))⁻¹).val * X))))
    (B : Std Small (fs.map RealBlock.character) →ₗ[ℂ] (H → ℂ))
    (hB : IsRealUniformWhittakerIntertwiner t (fs.map RealBlock.character) a B)
    (v : Std Small (fs.map RealBlock.character)) (f₁ : ℝ → ℂ) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (rate L : ℝ) (hrate : 0 < rate) :
    let f₂ (x : ℝ) := ordinaryWeight [RealBlock.character c] (fs.map RealBlock.character) a
      (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) 1 rate L (c₀ * x)
    let k₂ (x : ℝ) := reflectedWeight ([RealBlock.character c].map RealLocalJacquet.dualBlock)
      ((fs.map RealBlock.character).map RealLocalJacquet.dualBlock) rate L (c₀⁻¹ * x)
    let m₀ := D.measure.prod (ordinaryChartMeasure t q a D.groupHaar κ)
    let F := ordinarySeparatedKernel t q false a c T W (B v) f₁ f₂
    let Fm := ordinarySeparatedKernel t q true a c T W (B v) f₁ k₂
    Integrable F m₀ → Integrable Fm m₀ → (∫ p, F p ∂m₀) = (c₀ : ℂ) * ∫ p, Fm p ∂m₀ := by
  intro f₂ k₂ m₀ F Fm hF hFm
  let ν := D.groupHaar
  have hν : ν.IsHaarMeasure := D.groupHaar_isHaar
  have h₁ := integral_over_leading t q D a ν κ hν hκ F hF
  have h₂ := integral_over_leading t q D a ν κ hν hκ Fm hFm
  rw [h₁, h₂, ← integral_const_mul]
  apply integral_congr_ae
  refine ae_of_all _ fun p => ?_
  let C := retainedTail Small q (outerWithLeading Small q 1 p.2.1) p.2.2
  let g := p.1.out
  let Φ := leadingRestriction Small TailSize Small C T.leading
  let L₀ := retainedCoefficient t q a c T C * weightedOrdinary (rankLT t q) (ρ C⁻¹ W) (fun _ => 1) f₁ p.1
  have hEq := realGapSquareWeighted t D a c fs hfs Φ (hT _ _) B hB v g rate L hrate c₀ hc₀
  have hKey : (∫ y : H, realAdjacentMatrixWeight c.character.toMonoidHom Φ 0 y * B v (g * y) *
        f₂ (δ y) ∂ν) =
      (c₀ : ℂ) * ∫ y : H, realAdjacentMatrixWeight c.inverse.character.toMonoidHom
        (realRectangularSchwartzFourier a Φ) 0 (ι y) * B v (g * y) * k₂ (δ (ι y)) ∂ν := hEq
  dsimp only [F, Fm]
  simp_rw [ordinarySeparatedKernel_leading]
  simp only [Bool.false_eq_true, ↓reduceIte, leadingSide, squareLeading, sideCharacter]
  rw [integral_const_mul, integral_const_mul]
  change L₀ * (∫ y : H, realAdjacentMatrixWeight c.character.toMonoidHom Φ 0 y * B v (g * y) *
      f₂ (δ y) ∂ν) =
    (c₀ : ℂ) * (L₀ * (∫ y : H, realAdjacentMatrixWeight c.inverse.character.toMonoidHom
      (realRectangularSchwartzFourier a Φ) 0 (ι y) * B v (g * y) * k₂ (δ (ι y)) ∂ν))
  rw [hKey]
  ring

private def assembleLower (p : Side × (Q t × NativeLower)) : Dual :=
  (p.2.1, p.1.1, rectangleRows t q p.2.2, p.1.2)

private def lowerEquiv : Side × (Q t × NativeLower) ≃ᵐ Dual :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Side)
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Q t)) (rectangleRows t q))).trans
    (MeasurableEquiv.prodComm.trans (MeasurableEquiv.prodAssoc.trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Q t)) interchangeFirst)))

private theorem measurePreserving_lowerEquiv (D : RealQuotientMeasureData t) (a : ℝˣ)
    (η₁ : Measure H) (κ : Measure (KU Large)) (hη₁ : η₁.IsHaarMeasure) (hκ : κ.IsHaarMeasure) :
    MeasurePreserving (lowerEquiv t q)
      ((ordinaryChartMeasure t q a η₁ κ).prod (realUnequalDualMeasure (r := UpperIndex) (-a) D))
      (D.measure.prod (dualChartMeasure t q a η₁ κ)) := by
  let σ := unitOuterMeasure Small q (SD a) η₁ κ
  let η := entryHaar (SD a) TailSize
  let ξ := rectangularMeasure (SD a) q Small
  let ξ₀ := rectangularMeasure (SD a) (UpperIndex - Small) Small
  let : κ.IsHaarMeasure := hκ
  let : η₁.IsHaarMeasure := hη₁
  let : SecondCountableTopology (KU Large) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : (SD a).measure.IsAddHaarMeasure := (SD a).isAddHaar
  let : SigmaFinite (SD a).measure := inferInstance
  let : SigmaFinite (RealGapTriangularChart.outerMeasure Small q (SD a) η₁ κ) := by
    unfold RealGapTriangularChart.outerMeasure
    infer_instance
  let : SigmaFinite σ := SigmaFinite.withDensity _
  let : SigmaFinite η := entryHaar_sigmaFinite (SD a) TailSize
  let : SigmaFinite D.measure := sigmaFinite_quotient D
  let : ξ.IsAddHaarMeasure := rectangularMeasure_isAddHaar _ _ _
  let : ξ₀.IsAddHaarMeasure := rectangularMeasure_isAddHaar _ _ _
  let : SigmaFinite ξ := inferInstance
  let : SigmaFinite ξ₀ := inferInstance
  have hμ : realUnequalDualMeasure (r := UpperIndex) (-a) D = D.measure.prod ξ₀ := by
    unfold realUnequalDualMeasure
    rw [RealJacquet.selfDualMeasure_neg]
  rw [hμ]
  have h₁ := (MeasurePreserving.id (σ.prod η)).prod
    ((MeasurePreserving.id D.measure).prod (measurePreserving_rectangleRows t q (SD a)))
  have h₂ : MeasurePreserving Prod.swap ((σ.prod η).prod (D.measure.prod ξ))
      ((D.measure.prod ξ).prod (σ.prod η)) :=
    measurePreserving_swap
  have h₃ := measurePreserving_prodAssoc D.measure ξ (σ.prod η)
  have h₄ := (MeasurePreserving.id D.measure).prod (measurePreserving_interchangeFirst ξ σ η)
  exact h₄.comp (h₃.comp (h₂.comp h₁))

private theorem integral_over_lower (D : RealQuotientMeasureData t) (a : ℝˣ) (η₁ : Measure H)
    (κ : Measure (KU Large)) (hη₁ : η₁.IsHaarMeasure) (hκ : κ.IsHaarMeasure) (F : Dual → ℂ)
    (hF : Integrable F (D.measure.prod (dualChartMeasure t q a η₁ κ))) :
    (∫ p, F p ∂D.measure.prod (dualChartMeasure t q a η₁ κ)) =
      ∫ p : Side, (∫ u, F (assembleLower t q (p, u)) ∂realUnequalDualMeasure (r := UpperIndex) (-a) D)
        ∂ordinaryChartMeasure t q a η₁ κ := by
  let e := lowerEquiv t q
  have he := measurePreserving_lowerEquiv t q D a η₁ κ hη₁ hκ
  let : κ.IsHaarMeasure := hκ
  let : η₁.IsHaarMeasure := hη₁
  let : SigmaFinite (ordinaryChartMeasure t q a η₁ κ) := sigmaFinite_ordinaryChartMeasure t q a η₁ κ
  let : SigmaFinite D.measure := sigmaFinite_quotient D
  let : (SD (-a)).measure.IsAddHaarMeasure := (SD (-a)).isAddHaar
  let : (rectangularMeasure (SD (-a)) (UpperIndex - Small) Small).IsAddHaarMeasure :=
    rectangularMeasure_isAddHaar _ _ _
  let : SigmaFinite (realUnequalDualMeasure (r := UpperIndex) (-a) D) := by
    unfold realUnequalDualMeasure
    infer_instance
  have hi := he.integrable_comp_of_integrable hF
  exact (he.integral_comp e.measurableEmbedding F).symm.trans (integral_prod _ hi)

/-- The smaller unequal functional equation integrated at every retained and leading matrix. -/
theorem lowerIntegral_reflection (D : RealQuotientMeasureData t) (a : ℝˣ) (η₁ : Measure H)
    (κ : Measure (KU Large)) (hη₁ : η₁.IsHaarMeasure) (hκ : κ.IsHaarMeasure) (c : RealCharacterData)
    (ds es dds ees : List RealBlock) (eb : ℝˣ) (sc : ℝ≥0) (hsc : 0 < sc) (sign : ℂ)
    (T : GodementColumnFactors Small q)
    (B : Std Large ds →ₗ[ℂ] (G Large → ℂ)) (hB : IsRealUniformWhittakerIntertwiner UpperIndex ds (-a) B)
    (B' : Std Small es →ₗ[ℂ] (H → ℂ)) (hB' : IsRealUniformWhittakerIntertwiner t es a B')
    (hN : ∀ (p : Std Large ds) (p' : Std Small es),
      HasRealPairNormalizedGrowth ds es dds ees eb sc hsc sign
        (realUnequalIntegral (rankLT t q) D (B p) (B' p'))
        (realUnequalDualIntegral (rankLT t q) (-a) D (B p) (B' p')))
    (v : Std Large ds) (v' : Std Small es)
    (k₂ : ℝ → ℂ) (b : ℝ) (hb : 0 < b) (rate L : ℝ) (hrate : 0 < rate) :
    let f₁ (x : ℝ) := ordinaryWeight ds es eb sc hsc sign rate L (b * x)
    let k₁ (x : ℝ) := reflectedWeight dds ees rate L (b⁻¹ * x)
    let m₀ := D.measure.prod (ordinaryChartMeasure t q a η₁ κ)
    let md := D.measure.prod (dualChartMeasure t q a η₁ κ)
    let Fm := ordinarySeparatedKernel t q true a c T (B v) (B' v') f₁ k₂
    let Fd := dualSeparatedKernel t q a c T (B v) (B' v') k₁ k₂
    Integrable Fm m₀ → Integrable Fd md →
      detCharacter c.inverse.character.toMonoidHom (weylLong TailSize ℝ) * (∫ p, Fm p ∂m₀) =
        (b : ℂ) * ∫ p, Fd p ∂md := by
  intro f₁ k₁ m₀ md Fm Fd hFm hFd
  let S := detCharacter c.inverse.character.toMonoidHom (weylLong TailSize ℝ)
  let : κ.IsHaarMeasure := hκ
  let : η₁.IsHaarMeasure := hη₁
  let : SigmaFinite D.measure := sigmaFinite_quotient D
  let : SigmaFinite (ordinaryChartMeasure t q a η₁ κ) := sigmaFinite_ordinaryChartMeasure t q a η₁ κ
  have hd := integral_over_lower t q D a η₁ κ hη₁ hκ Fd hFd
  have hm := integral_prod_symm Fm hFm
  rw [hm, hd, ← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  refine ae_of_all _ fun p => ?_
  let z := p.1.1.1.1
  let C := retainedTail Small q p.1 p.2
  let Φ := leadingRestriction Small TailSize Small C T.leading
  let L₀ := retainedCoefficient t q a c T C *
    realAdjacentMatrixWeight c.inverse.character.toMonoidHom (realRectangularSchwartzFourier a Φ) 0 (ι z) *
      k₂ (δ (ι z))
  let W := ρ C⁻¹ (B v)
  let V := ρ z (B' v')
  have hB'' : IsRealUniformWhittakerIntertwiner t es (-(-a)) B' := by simpa only [neg_neg] using hB'
  have hL := (realUnequalWeightedTranslation UpperIndex t (rankLT t q) ds es dds ees (-a) eb sc hsc sign D
    B B' hB hB'' hN v v' C⁻¹ z rate L hrate hb).2.2
  have hscale (u : Q t × NativeLower) : weightedDual (rankLT t q) W V (fun x => (b : ℂ) * k₁ x) u =
      (b : ℂ) * weightedDual (rankLT t q) W V k₁ u := by unfold weightedDual; ring
  change (∫ x, weightedOrdinary (rankLT t q) W V f₁ x ∂D.measure) =
    ∫ y, weightedDual (rankLT t q) W V (fun x => (b : ℂ) * k₁ x) y
      ∂realUnequalDualMeasure (r := UpperIndex) (-a) D at hL
  simp_rw [hscale, integral_const_mul] at hL
  have hmF (x : Q t) : Fm (x, p) = L₀ * weightedOrdinary (rankLT t q) W V f₁ x := by
    unfold Fm ordinarySeparatedKernel
    simp only [leadingSide, squareLeading, sideCharacter, ite_true]
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
    (b : ℂ) * (∫ u, Fd (assembleLower t q (p, u)) ∂realUnequalDualMeasure (r := UpperIndex) (-a) D)
  simp_rw [hmF, hdF, integral_const_mul]
  rw [hL]
  ring

/-- The two scaled comparisons compose with the explicit tail Weyl scalar. -/
def RealGapScaleComparisonStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (a : ℝˣ) (κ : Measure (KU Large)), κ.IsHaarMeasure →
    ∀ (c : RealCharacterData) (ds dds ees : List RealBlock) (fs : List RealCharacterData),
      fs.length = Small →
    ∀ (eb : ℝˣ) (sc : ℝ≥0) (hsc : 0 < sc) (sign : ℂ) (T : GodementColumnFactors Small q),
    (∀ (p : Outer Small q) (Z : Tail), FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun u : O => fun X : M Small Small =>
        leadingRestriction Small TailSize Small (retainedTail Small q p Z) T.leading
          ((((Unitary.toUnits u : H))⁻¹).val * X)))) →
    ∀ (B : Std Large ds →ₗ[ℂ] (G Large → ℂ)), IsRealUniformWhittakerIntertwiner UpperIndex ds (-a) B →
    ∀ (B' : Std Small (fs.map RealBlock.character) →ₗ[ℂ] (H → ℂ)),
      IsRealUniformWhittakerIntertwiner t (fs.map RealBlock.character) a B' →
    (∀ (p : Std Large ds) (p' : Std Small (fs.map RealBlock.character)),
      HasRealPairNormalizedGrowth ds (fs.map RealBlock.character) dds ees eb sc hsc sign
        (realUnequalIntegral (rankLT t q) D (B p) (B' p'))
        (realUnequalDualIntegral (rankLT t q) (-a) D (B p) (B' p'))) →
    ∀ (v : Std Large ds) (v' : Std Small (fs.map RealBlock.character)) (b c₀ : ℝ), 0 < b → 0 < c₀ →
    ∀ (rate L : ℝ), 0 < rate →
      let f₁ (x : ℝ) := ordinaryWeight ds (fs.map RealBlock.character) eb sc hsc sign rate L (b * x)
      let f₂ (x : ℝ) := ordinaryWeight [RealBlock.character c] (fs.map RealBlock.character) a
        (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) 1 rate L (c₀ * x)
      let k₁ (x : ℝ) := reflectedWeight dds ees rate L (b⁻¹ * x)
      let k₂ (x : ℝ) := reflectedWeight ([RealBlock.character c].map RealLocalJacquet.dualBlock)
        ((fs.map RealBlock.character).map RealLocalJacquet.dualBlock) rate L (c₀⁻¹ * x)
      let m₀ := D.measure.prod (ordinaryChartMeasure t q a D.groupHaar κ)
      let md := D.measure.prod (dualChartMeasure t q a D.groupHaar κ)
      let F := ordinarySeparatedKernel t q false a c T (B v) (B' v') f₁ f₂
      let Fm := ordinarySeparatedKernel t q true a c T (B v) (B' v') f₁ k₂
      let Fd := dualSeparatedKernel t q a c T (B v) (B' v') k₁ k₂
      Integrable F m₀ → Integrable Fm m₀ → Integrable Fd md →
        detCharacter c.inverse.character.toMonoidHom (weylLong TailSize ℝ) * (∫ p, F p ∂m₀) =
          ((b * c₀ : ℝ) : ℂ) * ∫ p, Fd p ∂md

theorem realGapScaleComparison : RealGapScaleComparisonStatement t q := by
  intro D a κ hκ c ds dds ees fs hfs eb sc hsc sign T hT B hB B' hB' hN v v' b c₀ hb hc₀ rate L hrate
    f₁ f₂ k₁ k₂ m₀ md F Fm Fd hF hFm hFd
  let S := detCharacter c.inverse.character.toMonoidHom (weylLong TailSize ℝ)
  have hs : (∫ p, F p ∂m₀) = (c₀ : ℂ) * ∫ p, Fm p ∂m₀ :=
    squareIntegral_reflection t q D a κ hκ c fs hfs T (B v) hT B' hB' v' f₁ c₀ hc₀ rate L hrate hF hFm
  have hl : S * (∫ p, Fm p ∂m₀) = (b : ℂ) * ∫ p, Fd p ∂md :=
    lowerIntegral_reflection t q D a D.groupHaar κ D.groupHaar_isHaar hκ c ds (fs.map RealBlock.character)
      dds ees eb sc hsc sign T B hB B' hB' hN v v' k₂ b hb rate L hrate hFm hFd
  change S * (∫ p, F p ∂m₀) = _
  rw [hs, mul_left_comm S, hl, Complex.ofReal_mul]
  ring

end Langlands.Global.RankinSelbergGlobal.RealGapScaleComparison
