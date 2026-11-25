import Langlands.TraceFormula.AdelicRegularCentralizer
import Langlands.TraceFormula.SingleOrbitGeometricTrace
import Langlands.TraceFormula.GeneralLinearSimpleTraceFormulaStatement
import Langlands.TraceFormula.FinitePlacePositiveTensor

/-! # The simple trace formulas with a single isolated rational orbit -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported ENNReal

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.QuotientIntegration Langlands.JacquetLanglands Langlands.BaseChange
open Langlands.Analysis.OperatorIdeals AdelicGroupAutomorphism

universe u

section MeasureBlock

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H]

/-- The measure quantification in the geometric side of the simple trace formulas. -/
def SimpleTraceGeometricExpansion (R : Subgroup H) (θ : H →* H) (μH : Measure H)
    (f : H → ℂ) (t : ℂ) {m : ℕ} (r : Fin m → R) : Prop :=
  let C (j : Fin m) := twistedCentralizer θ (r j : H)
  let D (j : Fin m) := R.subgroupOf (C j)
  ∀ [∀ j, MeasurableSpace (LeftQuotient (C j))]
    [∀ j, BorelSpace (LeftQuotient (C j))]
    [∀ j, MeasurableSpace (LeftQuotient (D j))]
    [∀ j, BorelSpace (LeftQuotient (D j))]
    (μC : ∀ j, Measure (C j)) [∀ j, (μC j).IsMulRightInvariant]
    [∀ j, IsFiniteMeasureOnCompacts (μC j)] [∀ j, (μC j).IsOpenPosMeasure]
    (νC : ∀ j, Measure (LeftQuotient (C j))) (νD : ∀ j, Measure (LeftQuotient (D j))),
    (∀ j, IsCompatible (C j) μH (μC j) (νC j)) →
    (∀ j, IsCompatible (D j) (μC j) Measure.count (νD j)) →
    (∀ j, νD j Set.univ ≠ ⊤) ∧
    (∀ j, Integrable (twistedOrbitFunction θ (r j : H) f) (νC j)) ∧
    t = ∑ j, ((νD j Set.univ).toReal : ℂ) * twistedOrbitalIntegral θ (r j : H) (νC j) f

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

/-- The orbital integral for the orbital measure from the chosen geometric term. -/
def TwistedGeometricMeasures.orbitalValue {R : Subgroup H} {θ : H →* H} {r : H} {μH : Measure H}
    (d : TwistedGeometricMeasures R θ r μH) (f : H → ℂ) : ℂ :=
  twistedOrbitalIntegral θ r d.orbital f

set_option backward.isDefEq.respectTransparency.types false in
/-- A geometric expansion supplies its value for each family of bundled measures. -/
theorem bundledGeometricTraceSum (R : Subgroup H) (θ : H →* H) (μH : Measure H)
    (f : H → ℂ) (t : ℂ) {m : ℕ} (r : Fin m → R)
    (h : SimpleTraceGeometricExpansion R θ μH f t r)
    (d : ∀ j, TwistedGeometricMeasures R θ (r j : H) μH) :
    (∀ j, (d j).rational Set.univ ≠ ⊤) ∧ t = ∑ j, (d j).term f := by
  let C (j : Fin m) := twistedCentralizer θ (r j : H)
  let D (j : Fin m) := R.subgroupOf (C j)
  let mC : ∀ j, MeasurableSpace (LeftQuotient (C j)) :=
    fun j => leftQuotientMeasurableSpace (C j)
  let : ∀ j, BorelSpace (LeftQuotient (C j)) := fun j => leftQuotient_borelSpace (C j)
  let mD : ∀ j, MeasurableSpace (LeftQuotient (D j)) :=
    fun j => leftQuotientMeasurableSpace (D j)
  let : ∀ j, BorelSpace (LeftQuotient (D j)) := fun j => leftQuotient_borelSpace (D j)
  let μC : ∀ j, Measure (C j) := fun j => (d j).centralizer
  let : ∀ j, (μC j).IsMulRightInvariant := fun j => (d j).rightInvariant
  let : ∀ j, IsFiniteMeasureOnCompacts (μC j) := fun j => (d j).finiteOnCompacts
  let : ∀ j, (μC j).IsOpenPosMeasure := fun j => (d j).openPos
  have hh := h μC (fun j => (d j).orbital) (fun j => (d j).rational)
    (fun j => (d j).orbital_compatible) (fun j => (d j).rational_compatible)
  exact ⟨hh.1, hh.2.2⟩

end MeasureBlock

private local instance (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

private local instance (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option maxRecDepth 2600 in
/-- Exact ordinary simple trace formula after isolating one rational class. -/
def GeneralLinearSingleOrbitTraceStatement : Prop :=
  GeneralLinearSimpleTraceFormulaStatement.{u} →
  ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ)
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive GLₙ)
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ GLₙ)
    (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
    (hc : IsCentral i) [(Measure.haar : Measure (normOneSubgroup K GLₙ)).IsMulRightInvariant],
    let μG : Measure (AdelicGroupPoints K GLₙ) := Measure.haar
    ∀ f₁ f₂ : C_c(AdelicGroupPoints K GLₙ, ℂ),
      (∀ h₁ : Integrable f₁ μG,
        IsHilbertSchmidt (fullAEL2CuspidalIntegratedAction K GLₙ hPD hG T i hi I e hc μG f₁ h₁)) →
      (∀ h₂ : Integrable f₂ μG,
        IsHilbertSchmidt (fullAEL2CuspidalIntegratedAction K GLₙ hPD hG T i hi I e hc μG f₂ h₂)) →
      (∀ (P : ProperRationalParabolic GLₙ) (x y : AdelicGroupPoints K GLₙ),
        ∫ m, f₂ (x * (m : AdelicGroupPoints K GLₙ) * y)
          ∂properParabolicHaarMeasure K GLₙ hPD hG P = 0) →
    let f : AdelicGroupPoints K GLₙ → ℂ := fun g => ∫ a, f₁ a * f₂ (a⁻¹ * g) ∂μG
    ∀ v : Langlands.Global.FinitePlace K,
      (∀ g ∈ tsupport f, IsRegularElliptic (FiniteAdelicGL.localProjection K n v
        (AdelicGL.finite K n (GeneralLinearGroupPoints.adelicHomeomorph K n g)))) →
    let H := normOneSubgroup K GLₙ
    let R := rationalNormOneSubgroup K GLₙ
    let θ := MonoidHom.id H
    let fOne := normOnePositiveAverage K GLₙ T i
      (normalizedPositiveHaarMeasure K GLₙ T i hi I e hc) f
    ∀ (r₀ : R) (d₀ : TwistedGeometricMeasures R θ (r₀ : H) Measure.haar),
      (∀ q : R, (∃ x : H, fOne (x⁻¹ * (q : H) * x) ≠ 0) →
        IsTwistedConjugate R θ (q : H) (r₀ : H)) →
      ∃ h : Integrable f μG,
        let X := haarQuotientL2IntegratedAction K GLₙ T i hi I e hc μG f h
        IsTraceClass X ∧
        (d₀.orbitalValue fOne ≠ 0 → d₀.rational Set.univ ≠ ⊤) ∧
        operatorTrace X = d₀.term fOne

set_option maxRecDepth 3500 in
set_option maxHeartbeats 4200000 in
set_option backward.isDefEq.respectTransparency.types false in
theorem generalLinearSingleOrbitTrace : GeneralLinearSingleOrbitTraceStatement.{u} := by
  intro hTF K _ _ n hPD hG T i hi _ I _ e hc _ μG f₁ f₂ h₁ h₂ hP f v hEll
    H R θ fOne r₀ d₀ hIso
  obtain ⟨h, hClass, m, r, hDistinct, hReg, hCover, hSum⟩ :=
    hTF K n hPD hG T i hi I e hc f₁ f₂ h₁ h₂ hP v hEll
  let X := haarQuotientL2IntegratedAction K GLₙ T i hi I e hc μG f h
  let μH : Measure H := Measure.haar
  have hAvail (j : Fin m) : Nonempty (TwistedGeometricMeasures R θ (r j : H) μH) :=
    nonempty_twistedGeometricMeasures_of_commutative (isDiscrete_rationalNormOneSubgroup K GLₙ)
      continuous_id (generalLinearRegularCentralizerCommutative K n v (r j) (hReg j))
  have hBlock : SimpleTraceGeometricExpansion R θ μH fOne (operatorTrace X) r := hSum
  exact ⟨h, hClass, singleOrbitGeometricTrace r₀ d₀ fOne (operatorTrace X) r
    hDistinct (fun q hq => hCover q q.property hq) hIso hAvail
    (bundledGeometricTraceSum R θ μH fOne (operatorTrace X) r hBlock)⟩

end Langlands.TraceFormula
