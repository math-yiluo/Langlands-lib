import Langlands.TraceFormula.GeneralLinearSimpleTwistedTraceFormulaStatement
import Langlands.TraceFormula.GeneralLinearWeilTwistedEllipticRepresentatives
import Langlands.TraceFormula.GeneralLinearWeilTwistedClosedOrbitProof
import Langlands.TraceFormula.GeneralLinearWeilTwistedCompactQuotientProof
import Langlands.TraceFormula.GroupSchemeFullL2TraceClassProof
import Langlands.TraceFormula.GeneralLinearTensorSimpleTraceFormulaReduction
import Langlands.TraceFormula.GroupSchemeSimpleTwistedTraceFormula

/-! # The simple twisted trace formula for `Res_{L/K} GL_n` -/

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
open Langlands.BaseChange

namespace Langlands.TraceFormula

-- Keep the adelic group and its subgroup constructions opaque during elaboration.
attribute [local irreducible] Global.AdelicGroupPoints.normOneSubgroup
  Global.AdelicGroupPoints.rationalNormOneSubgroup
  AdelicGroupAutomorphism.normOneAut AdelicGroupAutomorphism.unitGaloisAut twistedCentralizer
  GroupScheme.AffineWeil.corepresentableBy GroupScheme.AffineWeil.tensorFunctor
  Global.AdelicGroupPoints.topologicalSpace

attribute [local instance] generalLinearSimpleTwistedTraceIsAffine
  generalLinearSimpleTwistedTraceSmooth

set_option hygiene false in
local notation "Wₙ" =>
  weilGroup K L (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K))

set_option hygiene false in
local notation "τ" =>
  unitGaloisAut K L (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)) σ

set_option hygiene false in
/-- The Haar convolution `f₁ * f₂`, for the bound variables `f₁` and `f₂`. -/
local notation "convₙ" => fun g => ∫ a, f₁ a * f₂ (a⁻¹ * g) ∂Measure.haar


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
/-- The simple twisted trace formula for `Res_{L/K} GL_n` and a cyclic extension `L/K`. -/
theorem generalLinearSimpleTwistedTraceFormula :
    GeneralLinearSimpleTwistedTraceFormulaStatement.{u} := by
  intro K _ _ L _ _ _ _ σ l hcyc n hPD hG T i hi _ I _ e hc _ hfix
  dsimp only
  intro f₁ f₂ hHS₁ hHS₂ hvan w hsupp
  -- trace class of `R(f)` and the formula on `L²([W])` for the convolution `f`
  obtain ⟨h, htr⟩ := groupSchemeFullL2TraceClass K _ hPD hG T i hi I e hc f₁ f₂ hHS₁ hHS₂ hvan
  have hcf := Langlands.Analysis.continuous_convolution_compactlySupported
    (Measure.haar : Measure (AdelicGroupPoints K Wₙ)) f₁ f₂
  have hcs := Langlands.Analysis.hasCompactSupport_convolution_compactlySupported
    (Measure.haar : Measure (AdelicGroupPoints K Wₙ)) f₁ f₂
  obtain ⟨hΘ, hΘμ, hformula⟩ := groupSchemeSimpleTwistedTraceFormula K Wₙ T i hi I e hc τ
    (isOfFinOrder_unitGaloisAut K L _ σ) hfix
  -- the rational twisted classes meeting the support
  let Ω : Set (normOneSubgroup K Wₙ) := normOneFactor K _ T i hi I e '' tsupport convₙ
  have hΩ : IsCompact Ω := hcs.isCompact.image (continuous_normOneFactor K _ T i hi I e)
  have hell : ∀ z ∈ Ω, IsRegularElliptic (FiniteAdelicGL.localProjection L n w
      (AdelicGL.finite L n (cyclicWeilAdelicMap K L n ((List.range l).map fun k =>
        adelicAut K (τ ^ k) (z : AdelicGroupPoints K Wₙ)).prod))) := by
    rintro z ⟨g, hg, rfl⟩
    have h1 := hsupp g hg
    rw [← positivePointMap_mul_normOneFactor K _ T i hi I e g] at h1
    have h2 := localNorm_positivePointMap_mul (σ := σ) (l := l) T i hi I e w
      (positiveFactor K _ T i hi I e g) (normOneFactor K _ T i hi I e g : AdelicGroupPoints K Wₙ)
    change IsRegularElliptic (FiniteAdelicGL.localProjection L n w (AdelicGL.finite L n
      (cyclicWeilAdelicMap K L n ((List.range l).map fun k =>
        adelicAut K (τ ^ k) (positivePointMap K _ T i (positiveFactor K _ T i hi I e g) *
          (normOneFactor K _ T i hi I e g : AdelicGroupPoints K Wₙ))).prod))) at h1
    rw [← h2]
    exact h1
  obtain ⟨m, r, hpair, hrell, hcover⟩ :=
    exists_twistedClass_representatives_of_isCompact hcyc w Ω hΩ hell
  -- closed twisted orbits and compact centralizer quotients of the representatives
  have hσ : ∀ j, ∃ δ : GeneralLinear n L,
      cyclicWeilAdelicMap K L n (r j).val.val = AdelicGL.rational L n δ ∧
        IsSigmaElliptic σ l δ := fun j =>
    exists_sigmaElliptic_rational_matrix_of_isRegularElliptic_localNorm
      generalLinearWeilAdelicTwist hcyc (r j) w (hrell j)
  choose δ hδr hδ using hσ
  have hclosed := fun j =>
    generalLinearWeilTwistedClosedOrbit K L σ l hcyc n (r j) (δ j) (hδr j) (hδ j)
  have hcompact := fun j =>
    generalLinearWeilTwistedCompactQuotient K L σ l hcyc n (r j) (δ j) (hδr j) (hδ j)
  have hF := hformula convₙ hcf hcs h htr m r hclosed hcompact hpair
  dsimp only at hF
  have hrell' : ∀ j, IsRegularElliptic (FiniteAdelicGL.localProjection L n w
      (AdelicGL.finite L n (GeneralLinearGroupPoints.adelicHomeomorph L n
        (AdelicGroupPoints.map L (AffineWeil.unitBaseChange K L
          (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)))
          (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of L))
          (GroupScheme.GeneralLinear.baseChangeIso (Fin n) (Spec.algebraMap K L)).hom
          (AdelicGaloisUnit.weilAdelicEquiv K L
            (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K))
            ((List.range l).map fun k =>
              adelicAut K (τ ^ k) ((r j : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ)).prod))))) :=
    hrell
  with_reducible refine ⟨hΘ, hΘμ, h, htr, m, r, hpair, hrell', ?cover, hF ?cover⟩
  rintro q hq ⟨x, hx⟩
  with_reducible apply hcover q hq
  refine ⟨x, ?_⟩
  obtain ⟨a, ha⟩ : ∃ a, convₙ (positivePointMap K _ T i a *
      ((x⁻¹ * q * normOneAut K τ x : normOneSubgroup K Wₙ) : AdelicGroupPoints K Wₙ)) ≠ 0 := by
    by_contra! hne
    exact hx (by simp only [hne, integral_zero])
  refine ⟨_, subset_tsupport _ ha, ?_⟩
  apply Subtype.ext
  change (positivePointMap K _ T i (positiveFactor K _ T i hi I e _))⁻¹ * _ = _
  rw [positiveFactor_mul_normOne, inv_mul_cancel_left]

end Langlands.TraceFormula
