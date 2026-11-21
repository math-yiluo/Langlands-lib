import Langlands.TraceFormula.SingleOrbitSimpleTrace
import Langlands.TraceFormula.GeneralLinearSimpleTwistedTraceFormulaStatement

/-! # The twisted simple trace formula on a single rational orbit -/

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

private theorem commutative_twistedCentralizer_toMonoidHom {H : Type*} [Group H]
    [TopologicalSpace H] (θ : H ≃ₜ* H) (r : H)
    (h : ∀ x y : twistedCentralizer θ r, x * y = y * x) :
    ∀ x y : twistedCentralizer θ.toMonoidHom r, x * y = y * x :=
  h

private theorem isTwistedConjugate_toMonoidHom_iff {H : Type*} [Group H]
    [TopologicalSpace H] (R : Subgroup H) (θ : H ≃ₜ* H) (r q : H) :
    IsTwistedConjugate R θ.toMonoidHom r q ↔ IsTwistedConjugate R θ r q :=
  Iff.rfl

private theorem exists_nonzero_twistedOrbit_toMonoidHom_iff {H : Type*} [Group H]
    [TopologicalSpace H] (θ : H ≃ₜ* H) (q : H) (f : H → ℂ) :
    (∃ x : H, f (x⁻¹ * q * θ.toMonoidHom x) ≠ 0) ↔
      (∃ x : H, f (x⁻¹ * q * θ x) ≠ 0) :=
  Iff.rfl

private theorem geometricExpansion_toMonoidHom {H : Type*} [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
    (R : Subgroup H) (θ : H ≃ₜ* H) (μH : Measure H) (f : H → ℂ) (t : ℂ)
    {m : ℕ} (r : Fin m → R)
    (h :
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
        t = ∑ j, ((νD j Set.univ).toReal : ℂ) * twistedOrbitalIntegral θ (r j : H) (νC j) f) :
    SimpleTraceGeometricExpansion R θ.toMonoidHom μH f t r :=
  @h

local instance (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "Wₙ" => weilGroup K L GLₙ

set_option maxRecDepth 3000 in
/-- Exact twisted simple trace formula after isolating one rational class. -/
def GeneralLinearSingleOrbitTwistedTraceStatement : Prop :=
  GeneralLinearSimpleTwistedTraceFormulaStatement.{u} →
  GeneralLinearWeilAdelicTwistStatement.{u} →
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (l : ℕ), IsCyclicAlgebra σ l →
    ∀ (n : ℕ) (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive Wₙ)
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ Wₙ)
    (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
    (hc : IsCentral i) [(Measure.haar : Measure (normOneSubgroup K Wₙ)).IsMulRightInvariant],
    i ≫ (unitGaloisAut K L GLₙ σ).hom = i →
    let H := normOneSubgroup K Wₙ
    let R := rationalNormOneSubgroup K Wₙ
    let μG : Measure (AdelicGroupPoints K Wₙ) := Measure.haar
    let Θ := adelicAut K (unitGaloisAut K L GLₙ σ)
    let θ := normOneAut K (unitGaloisAut K L GLₙ σ)
    let Φ : AdelicGroupPoints K Wₙ → AdelicGL L n := fun g =>
      GeneralLinearGroupPoints.adelicHomeomorph L n
        (AdelicGroupPoints.map L (AffineWeil.unitBaseChange K L GLₙ)
          (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of L))
          (GroupScheme.GeneralLinear.baseChangeIso (Fin n) (Spec.algebraMap K L)).hom
          (AdelicGaloisUnit.weilAdelicEquiv K L GLₙ g))
    let N : AdelicGroupPoints K Wₙ → AdelicGroupPoints K Wₙ := fun g =>
      ((List.range l).map fun k => adelicAut K (unitGaloisAut K L GLₙ σ ^ k) g).prod
    ∀ f₁ f₂ : C_c(AdelicGroupPoints K Wₙ, ℂ),
      (∀ h₁ : Integrable f₁ μG,
        IsHilbertSchmidt (fullAEL2CuspidalIntegratedAction K Wₙ hPD hG T i hi I e hc μG f₁ h₁)) →
      (∀ h₂ : Integrable f₂ μG,
        IsHilbertSchmidt (fullAEL2CuspidalIntegratedAction K Wₙ hPD hG T i hi I e hc μG f₂ h₂)) →
      (∀ (P : ProperRationalParabolic Wₙ) (x y : AdelicGroupPoints K Wₙ),
        ∫ m, f₂ (x * (m : AdelicGroupPoints K Wₙ) * y)
          ∂properParabolicHaarMeasure K Wₙ hPD hG P = 0) →
    let f : AdelicGroupPoints K Wₙ → ℂ := fun g => ∫ a, f₁ a * f₂ (a⁻¹ * g) ∂μG
    ∀ w : Langlands.Global.FinitePlace L,
      (∀ g ∈ tsupport f, IsRegularElliptic (FiniteAdelicGL.localProjection L n w
        (AdelicGL.finite L n (Φ (N g))))) →
    let fOne : H → ℂ := fun x =>
      ∫ a, f (positivePointMap K Wₙ T i a * (x : AdelicGroupPoints K Wₙ))
        ∂normalizedPositiveHaarMeasure K Wₙ T i hi I e hc
    ∀ (r₀ : R) (d₀ : TwistedGeometricMeasures R θ.toMonoidHom (r₀ : H) Measure.haar),
      (∀ q : R, (∃ x : H, fOne (x⁻¹ * (q : H) * θ x) ≠ 0) →
        IsTwistedConjugate R θ (q : H) (r₀ : H)) →
      ∃ (hΘ : ∀ x, Θ x ∈ positiveRationalSubgroup K Wₙ T i ↔
          x ∈ positiveRationalSubgroup K Wₙ T i)
        (hΘμ : MeasurePreserving (quotientAutomorphism (positiveRationalSubgroup K Wₙ T i) Θ hΘ).symm
          (positiveRationalQuotientHaarMeasure K Wₙ T i)
          (positiveRationalQuotientHaarMeasure K Wₙ T i))
        (h : Integrable f μG),
        let X := haarQuotientL2IntegratedAction K Wₙ T i hi I e hc μG f h
        let S := twistOperator (positiveRationalSubgroup K Wₙ T i) Θ hΘ
          (positiveRationalQuotientHaarMeasure K Wₙ T i) hΘμ
        IsTraceClass X ∧
        (d₀.orbitalValue fOne ≠ 0 → d₀.rational Set.univ ≠ ⊤) ∧
        operatorTrace (X.comp S) = d₀.term fOne

set_option maxRecDepth 3700 in
set_option maxHeartbeats 4500000 in
theorem generalLinearSingleOrbitTwistedTrace : GeneralLinearSingleOrbitTwistedTraceStatement.{u} := by
  intro hTF hWeil K _ _ L _ _ _ _ σ l hσ n hPD hG T i hi _ I _ e hc _ hFix
    H R μG Θ θ Φ N f₁ f₂ h₁ h₂ hP f w hEll fOne r₀ d₀ hIso
  have hTF₀ := hTF K L σ l hσ n
  have hTF₁ := hTF₀ hPD hG T i hi I e hc hFix
  have hTFTests := hTF₁ f₁ f₂
  dsimp only [μG] at h₁ h₂
  have hTFHS₁ := hTFTests (by with_reducible exact h₁)
  have hTFHS₂ := hTFHS₁ (by with_reducible exact h₂)
  have hTF₂ := hTFHS₂ (by
    intro P x y
    exact hP P x y)
  have hTF₃ := hTF₂ w (by with_reducible exact hEll)
  obtain ⟨hΘ, hΘμ, h, hClass, m, r, hDistinct, hReg, hCover, hSum⟩ := hTF₃
  let X := haarQuotientL2IntegratedAction K Wₙ T i hi I e hc μG f (by with_reducible exact h)
  let S := twistOperator (positiveRationalSubgroup K Wₙ T i) Θ hΘ
    (positiveRationalQuotientHaarMeasure K Wₙ T i) (by with_reducible exact hΘμ)
  let μH : Measure H := Measure.haar
  let N' (g : AdelicGroupPoints K Wₙ) :=
    ((List.range l).map fun k => adelicAut K (unitGaloisAut K L GLₙ (σ ^ k)) g).prod
  have hN (g : AdelicGroupPoints K Wₙ) : N g = N' g := by
    have hPow (k : ℕ) : unitGaloisAut K L GLₙ σ ^ k = unitGaloisAut K L GLₙ (σ ^ k) := by
      simpa only [unitGaloisAutHom_apply] using (map_pow (unitGaloisAutHom K L GLₙ) σ k).symm
    with_reducible
      exact congrArg List.prod (List.map_congr_left fun k _ =>
        congrArg (fun a => adelicAut K a g) (hPow k))
  have hReg' (j : Fin m) : IsRegularElliptic (FiniteAdelicGL.localProjection L n w
      (AdelicGL.finite L n (Φ (N' ((r j : H) : AdelicGroupPoints K Wₙ))))) :=
    hN ((r j : H) : AdelicGroupPoints K Wₙ) ▸ (by with_reducible exact hReg j)
  have hCommAll := generalLinearTwistedRegularCentralizerCommutative.{u}
  unfold GeneralLinearTwistedRegularCentralizerCommutativeStatement at hCommAll
  have hCommFields := hCommAll hWeil K L σ l hσ n
  have hCommPlace := hCommFields w
  have hAvail (j : Fin m) : Nonempty
      (@TwistedGeometricMeasures H _ _ _ _ _ R θ.toMonoidHom (r j).val μH) := by
    have hCommRep := hCommPlace (by with_reducible exact r j)
    have hComm := hCommRep (by with_reducible exact hReg' j)
    exact nonempty_twistedGeometricMeasures_of_commutative (Γ := R) (θ := θ.toMonoidHom)
      (δ := (r j).val) (μG := μH) (isDiscrete_rationalNormOneSubgroup K Wₙ)
      θ.continuous
      (commutative_twistedCentralizer_toMonoidHom θ (r j).val (by with_reducible exact hComm))
  have hBlock := @geometricExpansion_toMonoidHom _ _ _ _ _ _ _ _ _ _ _ m r (@hSum)
  have hTrace := bundledGeometricTraceSum R θ.toMonoidHom μH fOne (operatorTrace (X.comp S)) r (by
    dsimp only [R, θ, μH, fOne, X, S, μG, f, Θ]
    with_reducible exact @hBlock)
  have hSingle := singleOrbitGeometricTrace r₀ d₀ fOne (operatorTrace (X.comp S)) r
    (fun j k hjk => hDistinct j k ((isTwistedConjugate_toMonoidHom_iff R θ (r j).val (r k).val).mp hjk))
    (by
      intro q hq
      have hq' := (exists_nonzero_twistedOrbit_toMonoidHom_iff θ q.val fOne).mp hq
      dsimp only [fOne] at hq'
      obtain ⟨j, hj⟩ := hCover q q.property (by with_reducible exact hq')
      exact ⟨j, (isTwistedConjugate_toMonoidHom_iff R θ (r j).val q.val).mpr hj⟩)
    hIso hAvail hTrace
  refine ⟨hΘ, hΘμ, h, hClass, ?_, ?_⟩
  · unfold TwistedGeometricMeasures.orbitalValue
    exact hSingle.1
  · with_reducible exact hSingle.2

end Langlands.TraceFormula
