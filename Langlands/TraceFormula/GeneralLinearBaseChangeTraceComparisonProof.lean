import Langlands.TraceFormula.GeneralLinearBaseChangeTermMatching
import Langlands.TraceFormula.SingleOrbitSimpleTrace
import Langlands.TraceFormula.GeneralLinearSimpleTraceFormulaProof
import Langlands.TraceFormula.GeneralLinearSimpleTwistedTraceFormulaProof
import Langlands.TraceFormula.GeneralLinearBaseChangeTraceComparisonStatement

/-!
# Proof of the comparison of the simple trace formula for `GL_n` with its twisted form

The simple twisted trace formula for `Res_{L/K} GL_n` and the simple trace formula for `GL_n`
express both traces as finite geometric expansions. Their terms are compared through the norm
relation `BaseChangeNormRelated`, and the twisted expansion equals `c` times the ordinary one.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.QuotientIntegration Langlands.JacquetLanglands
open Langlands.Analysis.OperatorIdeals
open Langlands.TraceFormula.AdelicGroupAutomorphism
open Langlands.BaseChange Langlands.Global.AdelicFunctoriality

namespace Langlands.TraceFormula

/-- The geometric side of the simple twisted trace formula, stated with a topological group
automorphism, is a geometric expansion for the underlying monoid homomorphism. -/
private theorem baseChangeGeometricExpansion_toMonoidHom {H : Type*} [Group H]
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

local instance baseChangeComparisonProofIsAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance baseChangeComparisonProofSmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "Wₙ" => weilGroup K L GLₙ

set_option hygiene false in
local notation "Θₙ" => normOneAut K (unitGaloisAut K L GLₙ σ)

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

set_option maxRecDepth 4000 in
set_option maxHeartbeats 24000000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The comparison of the simple twisted trace formula for `Res_{L/K} GL_n` with the simple
trace formula for `GL_n`: `tr (R(φ) ∘ I_θ) = c · tr R(f)`. -/
theorem generalLinearBaseChangeTraceComparison :
    GeneralLinearBaseChangeTraceComparisonStatement.{u} := by
  intro K _ _ L _ _ _ _ σ l hσ n hPD hW TW iW hiW _ IW _ eW hcW _ hFix
    hG TG iG hiG _ IG _ eG hcG _ μW μG Θ θ Φ N incl ΦG
    φ₁ φ₂ hφ₁ hφ₂ hφP φ w hφEll f₁ f₂ hf₁ hf₂ hfP f v hfEll φOne fOne c hMatch hOff
  dsimp only [μW] at hφ₁ hφ₂
  dsimp only [μG] at hf₁ hf₂
  have hTW := generalLinearSimpleTwistedTraceFormula K L σ l hσ n hPD hW TW iW hiW IW eW hcW
    hFix φ₁ φ₂ (by with_reducible exact hφ₁) (by with_reducible exact hφ₂)
    (fun P x y => hφP P x y) w (by with_reducible exact hφEll)
  obtain ⟨hΘ, hΘμ, hφ, hClassW, m, r, hrD, hrReg, hrC, hrSum⟩ := hTW
  have hTG := generalLinearSimpleTraceFormula K n hPD hG TG iG hiG IG eG hcG f₁ f₂
    (by with_reducible exact hf₁) (by with_reducible exact hf₂)
    (fun P x y => hfP P x y) v (by with_reducible exact hfEll)
  obtain ⟨hf, hClassG, m', q, hqD, hqReg, hqC, hqSum⟩ := hTG
  refine ⟨hΘ, hΘμ, hφ, hf, hClassW, hClassG, ?_⟩
  have hBlockW := @baseChangeGeometricExpansion_toMonoidHom _ _ _ _ _ _ _ _ _ _ _ m r (@hrSum)
  have hBlockG : SimpleTraceGeometricExpansion (rationalNormOneSubgroup K GLₙ)
      (MonoidHom.id (normOneSubgroup K GLₙ)) Measure.haar fOne
      (operatorTrace (haarQuotientL2IntegratedAction K GLₙ TG iG hiG IG eG hcG μG f hf)) q :=
    hqSum
  have hT := fun d => (bundledGeometricTraceSum _ _ _ _ _ r hBlockW d).2
  have hU := fun d => (bundledGeometricTraceSum _ _ _ _ _ q hBlockG d).2
  let regW : rationalNormOneSubgroup K Wₙ → Prop := fun x =>
    IsRegularElliptic (FiniteAdelicGL.localProjection L n w
      (AdelicGL.finite L n (cyclicWeilAdelicMap K L n (((List.range l).map fun k =>
        adelicAut K (unitGaloisAut K L GLₙ σ ^ k)
          ((x : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ)).prod))))
  let regG : rationalNormOneSubgroup K GLₙ → Prop := fun y =>
    IsRegularElliptic (FiniteAdelicGL.localProjection K n v
      (AdelicGL.finite K n (GeneralLinearGroupPoints.adelicHomeomorph K n
        ((y : normOneSubgroup K GLₙ) : AdelicGroupPoints K GLₙ))))
  have hrReg' : ∀ j, regW (r j) := hrReg
  have hqReg' : ∀ k, regG (q k) := hqReg
  have hrM (j : Fin m) : Nonempty (TwistedGeometricMeasures (rationalNormOneSubgroup K Wₙ)
      (Θₙ).toMonoidHom ((r j : rationalNormOneSubgroup K Wₙ) : normOneSubgroup K Wₙ)
      Measure.haar) :=
    nonempty_twistedGeometricMeasures_baseChange hσ w v (r j) (hrReg' j)
  have hqM (k : Fin m') : Nonempty (TwistedGeometricMeasures (rationalNormOneSubgroup K GLₙ)
      (MonoidHom.id (normOneSubgroup K GLₙ))
      ((q k : rationalNormOneSubgroup K GLₙ) : normOneSubgroup K GLₙ) Measure.haar) :=
    nonempty_twistedGeometricMeasures_of_commutative (isDiscrete_rationalNormOneSubgroup K GLₙ)
      continuous_id (generalLinearRegularCentralizerCommutative K n v (q k) (hqReg k))
  have hMatch' := baseChange_termMatch hσ w v φOne fOne c hMatch
  have hOff' := baseChange_orbitalIntegral_eq_zero σ l v fOne hOff
  refine geometricExpansion_eq_mul_of_termPairing_continuousMulEquiv
    (rationalNormOneSubgroup K Wₙ) (rationalNormOneSubgroup K GLₙ) (Θₙ) Measure.haar
    Measure.haar φOne fOne c _ _
    (fun x y => BaseChangeNormRelated σ l (x : normOneSubgroup K Wₙ)
      (y : normOneSubgroup K GLₙ))
    regW regG r q ?hT ?hU ?hrD ?hqD ?hrC ?hqC ?hrReg ?hqReg ?hrM ?hqM ?hNorm ?hAW ?hAG ?hUW
    ?hUG ?hMatchW ?hMatchG ?hOff
  case hT =>
    exact hT
  case hU =>
    exact hU
  case hrD =>
    exact hrD
  case hqD =>
    exact hqD
  case hrC =>
    exact hrC
  case hqC =>
    exact hqC
  case hrReg =>
    exact hrReg'
  case hqReg =>
    exact hqReg'
  case hrM =>
    exact hrM
  case hqM =>
    exact hqM
  case hOff =>
    exact fun y hy hnone => hOff' y hy hnone
  case hMatchG =>
    exact fun x y hA hreg => (hMatch' x y hA hreg).2
  case hMatchW =>
    exact fun x y hA hreg => (hMatch' x y hA hreg).1
  case hNorm =>
    exact fun x _ => exists_baseChangeNormRelated σ l hσ x
  case hAG =>
    exact baseChangeNormRelated_of_conj_right σ l hσ
  case hUG =>
    exact isConjugate_of_baseChangeNormRelated σ l hσ
  case hAW =>
    exact baseChangeNormRelated_of_twistedConj_left σ l hσ
  case hUW =>
    exact isTwistedConjugate_of_baseChangeNormRelated σ l hσ

end Langlands.TraceFormula
