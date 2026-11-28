import Langlands.TraceFormula.CalibratedTraceExtraction
import Langlands.TraceFormula.NormOneFinitePlaceGeometricTerm

/-! # Calibrating two isolated norm-one trace formulas at a finite place -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme Langlands.QuotientIntegration Langlands.BaseChange
open AdelicGroupAutomorphism

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u

variable (K : Type u) [Field K] [NumberField K]
  (G W : GroupScheme (Spec (CommRingCat.of K)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine W.X.left] [LocallyOfFiniteType W.X.hom]
  (v : FinitePlace K)
  (T : CommGroupScheme (Spec (CommRingCat.of K)))
  (iG : T.toGrp ⟶ G) (hiG : Function.Injective (characterRestrict iG))
  [(characterRestrict iG).range.FiniteIndex]
  (iW : T.toGrp ⟶ W) (hiW : Function.Injective (characterRestrict iW))
  [(characterRestrict iW).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
  (hcG : IsCentral iG) (hcW : IsCentral iW)

local notation "HG" => normOneSubgroup K G
local notation "HW" => normOneSubgroup K W
local notation "MG" => PlaceGroupPoints K G (Sum.inr v)
local notation "MW" => PlaceGroupPoints K W (Sum.inr v)

set_option maxRecDepth 4000 in
/-- Two trace identities with the same scalar give equality at the distinguished
finite place if the first pair agrees there and its isolated ordinary trace is nonzero.
On each side the exterior factor and the local quotient measure are fixed across the
two tests. -/
def NormOneFinitePlaceCalibratedTraceStatement : Prop :=
  let μHG : Measure HG := Measure.haar
  let μHW : Measure HW := Measure.haar
  let RG := rationalNormOneSubgroup K G
  let RW := rationalNormOneSubgroup K W
  let DG := normOneFinitePlaceDecomposition K G v T iG hiG I e hcG
  let DW := normOneFinitePlaceDecomposition K W v T iW hiW I e hcW
  ∀ [MeasurableSpace MG] [BorelSpace MG] [MeasurableSpace MW] [BorelSpace MW]
    [μHG.IsMulRightInvariant] [μHW.IsMulRightInvariant]
    (aG : Aut G) (aW : Aut W),
    iG ≫ aG.asIso.hom = iG → iW ≫ aW.asIso.hom = iW →
    ∀ (rG : RG) (rW : RW),
    let θG := (normOneAut K aG).toMonoidHom
    let θW := (normOneAut K aW).toMonoidHom
    let θvG := G.affinePointsTarget aG.asIso.hom (placeCompletion K (.inr v))
    let θvW := W.affinePointsTarget aW.asIso.hom (placeCompletion K (.inr v))
    let CvG := twistedCentralizer θvG (DG.symm (rG : HG)).1
    let CvW := twistedCentralizer θvW (DW.symm (rW : HW)).1
    (∀ x y : twistedCentralizer θG (rG : HG), x * y = y * x) →
    (∀ x y : twistedCentralizer θW (rW : HW), x * y = y * x) →
    ∀ (μvG : Measure MG) [μvG.IsHaarMeasure] (μvW : Measure MW) [μvW.IsHaarMeasure]
    (μCvG : Measure CvG) [μCvG.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μCvG]
    [μCvG.IsOpenPosMeasure] (μCvW : Measure CvW) [μCvW.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μCvW] [μCvW.IsOpenPosMeasure]
    (νvG : Measure (LeftQuotient CvG)) (νvW : Measure (LeftQuotient CvW)),
    IsCompatible CvG μvG μCvG νvG → IsCompatible CvW μvW μCvW νvW →
    ∀ (gG : AdelicGroupPoints K G → ℂ) (gW : AdelicGroupPoints K W → ℂ),
    (∀ z x, gG (z * finitePlacePointInclusion K G v x) = gG z) →
    (∀ z x, gW (z * finitePlacePointInclusion K W v x) = gW z) →
    ∀ (fG : Bool → MG → ℂ) (fW : Bool → MW → ℂ),
    let F₁ (j : Bool) := normOnePositiveAverage K G T iG
      (normalizedPositiveHaarMeasure K G T iG hiG I e hcG)
      (fun x => fG j (atPlace K G (.inr v) x) * gG x)
    let F₂ (j : Bool) := normOnePositiveAverage K W T iW
      (normalizedPositiveHaarMeasure K W T iW hiW I e hcW)
      (fun x => fW j (atPlace K W (.inr v) x) * gW x)
    let OG (j : Bool) := twistedOrbitalIntegral θvG (DG.symm (rG : HG)).1 νvG (fG j)
    let OW (j : Bool) := twistedOrbitalIntegral θvW (DW.symm (rW : HW)).1 νvW (fW j)
    ∀ (ordinaryTrace twistedTrace : Bool → ℂ) (c : ℂ), c ≠ 0 →
    (∀ (j : Bool) (d : TwistedGeometricMeasures RG θG (rG : HG) μHG),
      ordinaryTrace j = d.term (F₁ j)) →
    (∀ (j : Bool) (d : TwistedGeometricMeasures RW θW (rW : HW) μHW),
      twistedTrace j = d.term (F₂ j)) →
    (∀ j, twistedTrace j = c * ordinaryTrace j) →
    ordinaryTrace false ≠ 0 → OW false = OG false → OW true = OG true

set_option maxRecDepth 4200 in
set_option maxHeartbeats 3000000 in
set_option backward.isDefEq.respectTransparency.types false in
theorem normOneFinitePlaceCalibratedTrace :
    NormOneFinitePlaceCalibratedTraceStatement K G W v T iG hiG iW hiW I e hcG hcW := by
  unfold NormOneFinitePlaceCalibratedTraceStatement
  intro μHG μHW RG RW DG DW _ _ _ _ _ _ aG aW haG haW rG rW θG θW θvG θvW CvG CvW
    hCommG hCommW μvG _ μvW _ μCvG _ _ _ μCvW _ _ _ νvG νvW hνG hνW
    gG gW hgG hgW fG fW F₁ F₂ OG OW ordinaryTrace twistedTrace c hc hG hW hCompare hNonzero hCal
  obtain ⟨νjG, dG, _, _, _, hFactorG⟩ :=
    normOneFinitePlaceGeometricTerm K G v T iG hiG I e hcG aG haG rG hCommG μvG μCvG νvG hνG
  obtain ⟨νjW, dW, _, _, _, hFactorW⟩ :=
    normOneFinitePlaceGeometricTerm K W v T iW hiW I e hcW aW haW rW hCommW μvW μCvW νvW hνW
  let JG := (normOneFinitePlaceProjection K G v).toMonoidHom.ker
  let JW := (normOneFinitePlaceProjection K W v).toMonoidHom.ker
  let extG := twistedOrbitalIntegral (normOneFinitePlaceKernelTwist K G v aG).toMonoidHom
    (DG.symm (rG : HG)).2 νjG (fun z : JG => normOnePositiveAverage K G T iG
      (normalizedPositiveHaarMeasure K G T iG hiG I e hcG) gG z.val)
  let extW := twistedOrbitalIntegral (normOneFinitePlaceKernelTwist K W v aW).toMonoidHom
    (DW.symm (rW : HW)).2 νjW (fun z : JW => normOnePositiveAverage K W T iW
      (normalizedPositiveHaarMeasure K W T iW hiW I e hcW) gW z.val)
  have hOrbG (j : Bool) : dG.orbitalValue (F₁ j) = OG j * extG :=
    (hFactorG gG hgG (fG j)).1
  have hOrbW (j : Bool) : dW.orbitalValue (F₂ j) = OW j * extW :=
    (hFactorW gW hgW (fW j)).1
  have hTermG : ordinaryTrace false =
      ((dG.rational Set.univ).toReal : ℂ) * (OG false * extG) := by
    rw [hG false dG]
    change ((dG.rational Set.univ).toReal : ℂ) * dG.orbitalValue (F₁ false) = _
    rw [hOrbG]
  have hProduct : OG false * extG ≠ 0 := by
    intro hZero
    exact hNonzero (by rw [hTermG, hZero, mul_zero])
  have hExt : extG ≠ 0 := fun hZero => hProduct (by rw [hZero, mul_zero])
  have hLocal : OG false ≠ 0 := fun hZero => hProduct (by rw [hZero, zero_mul])
  have hFinite : dG.rational Set.univ ≠ ⊤ := by
    intro hTop
    exact hNonzero (by rw [hTermG, hTop, ENNReal.toReal_top, Complex.ofReal_zero, zero_mul])
  exact calibratedTraceExtraction RG RW θG θW (rG : HG) (rW : HW) μHG μHW dG dW
    F₁ F₂ ordinaryTrace twistedTrace OG OW extG extW c hExt hc hLocal hCal hOrbG hOrbW
    (fun _ => hFinite) (fun j => hG j dG) (fun j => hW j dW) hCompare

end Langlands.TraceFormula
