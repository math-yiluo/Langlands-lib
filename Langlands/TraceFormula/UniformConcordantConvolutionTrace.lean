import Langlands.Analysis.ConvolutionIntegral
import Langlands.Representation.Unitary.IntegratedConvolutionProof
import Langlands.TraceFormula.GeneralLinearBaseChangeGlobalMatchingStatement
import Langlands.TraceFormula.GeneralLinearBaseChangeTraceComparisonStatement
import Langlands.TraceFormula.GroupSchemeCuspidalImageProof
import Langlands.TraceFormula.GroupSchemeTwistedCuspidalSpectralExpansionProof

/-! # A uniform cuspidal trace comparison for locally concordant convolutions -/

noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj CompactlySupported
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Analysis Langlands.Analysis.OperatorIdeals
open Langlands.QuotientIntegration Langlands.JacquetLanglands
open Langlands.TraceFormula.AdelicGroupAutomorphism
open Langlands.BaseChange Langlands.Hecke
open scoped Langlands.TraceFormula.PlaceCompletion

namespace Langlands.TraceFormula

section CuspidalCompression

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom] (hPD : ParabolicDynamicStatement.{u})
  (hG : IsConnectedReductive G)
  (Z : CommGroupScheme (Spec (CommRingCat.of F))) (i : Z.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : Z.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
  (hc : IsCentral i) [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

local notation "A" => AdelicGroupPoints F G
local notation "m" => (Measure.haar : Measure A)
local notation "H" => Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G Z i)
local notation "S" => fullAEL2CuspidalSubmodule F G hPD hG Z i hi I e hc
local notation "R" => haarQuotientL2IntegratedAction F G Z i hi I e hc m

set_option backward.isDefEq.respectTransparency false in
/-- If the second convolution factor has vanishing radical integrals, composing the
convolution operator on the right by a bounded operator leaves its range cuspidal.
For a trace-class convolution operator the trace is therefore its cuspidal trace. -/
theorem cuspidalCompressionTraceOfConvolution
    (f₁ f₂ : C_c(A, ℂ)) (hf : Integrable (convolutionIntegral m f₁ f₂) m)
    (hvanish : ∀ (P : ProperRationalParabolic G) (x y : A),
      ∫ n, f₂ (x * (n : A) * y) ∂properParabolicHaarMeasure F G hPD hG P = 0)
    (htrace : IsTraceClass (R (convolutionIntegral m f₁ f₂) hf)) (U : H →L[ℂ] H) :
    operatorTrace ((S).orthogonalProjectionOnto ∘L
        (R (convolutionIntegral m f₁ f₂) hf ∘L U) ∘L (S).subtypeL) =
      operatorTrace (R (convolutionIntegral m f₁ f₂) hf ∘L U) := by
  have hf₁ : Integrable f₁ m := f₁.continuous.integrable_of_hasCompactSupport f₁.hasCompactSupport
  have hf₂ : Integrable f₂ m := f₂.continuous.integrable_of_hasCompactSupport f₂.hasCompactSupport
  obtain ⟨h, hconv⟩ := integratedActionConvolution A H m
    (haarQuotientL2BoundedRightAction F G Z i hi I e hc)
    (norm_haarQuotientL2BoundedRightAction F G Z i hi I e hc)
    (haarQuotientL2Orbit_aestronglyMeasurable F G Z i hi I e hc m) f₁ f₂ hf₁ hf₂
  change R (convolutionIntegral m f₁ f₂) hf = R f₁ hf₁ ∘L R f₂ hf₂ at hconv
  have hRange (x : H) : R (convolutionIntegral m f₁ f₂) hf x ∈ S := by
    rw [hconv, ContinuousLinearMap.comp_apply]
    exact haarQuotientL2IntegratedAction_mem_fullAEL2CuspidalSubmodule F G hPD hG Z i hi I e hc
      m f₁ hf₁ _ (groupSchemeCuspidalImage F G hPD hG Z i hi I e hc f₂ hf₂ hvanish x)
  exact (compression_trace_of_range S _ (isTraceClass_precomp _ U htrace)
    (fun x => hRange (U x))).2

set_option backward.isDefEq.respectTransparency false in
/-- The integrated cuspidal action of the same convolution has the ambient trace. -/
theorem cuspidalIntegratedTraceOfConvolution
    (f₁ f₂ : C_c(A, ℂ)) (hf : Integrable (convolutionIntegral m f₁ f₂) m)
    (hvanish : ∀ (P : ProperRationalParabolic G) (x y : A),
      ∫ n, f₂ (x * (n : A) * y) ∂properParabolicHaarMeasure F G hPD hG P = 0)
    (htrace : IsTraceClass (R (convolutionIntegral m f₁ f₂) hf)) :
    operatorTrace
      (fullAEL2CuspidalIntegratedAction F G hPD hG Z i hi I e hc m _ hf) =
      operatorTrace (R (convolutionIntegral m f₁ f₂) hf) := by
  have hCompression := eq_compression_of_val (S)
    (R (convolutionIntegral m f₁ f₂) hf)
    (fullAEL2CuspidalIntegratedAction F G hPD hG Z i hi I e hc m _ hf)
    (fullAEL2CuspidalIntegratedAction_val F G hPD hG Z i hi I e hc m _ hf)
  have h := cuspidalCompressionTraceOfConvolution F G hPD hG Z i hi I e hc f₁ f₂ hf hvanish
    htrace (ContinuousLinearMap.id ℂ _)
  rw [hCompression]
  simpa only [ContinuousLinearMap.comp_id] using h

end CuspidalCompression

local instance uniformIsAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance uniformSmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

local instance uniformPlaceMeasurable (K : Type u) [Field K] [NumberField K]
    (n : ℕ) (i : Place K) : MeasurableSpace (GeneralLinear n (placeCompletion K i)) := borel _

local instance uniformPlaceBorel (K : Type u) [Field K] [NumberField K]
    (n : ℕ) (i : Place K) : BorelSpace (GeneralLinear n (placeCompletion K i)) := ⟨rfl⟩

local instance uniformWeilPlaceMeasurable (K L : Type u) [Field K] [Field L] [NumberField K]
    [Algebra K L] [FiniteDimensional K L] (n : ℕ) (i : Place K) :
    MeasurableSpace (GeneralLinear n (LocalBaseChangeAlgebra K L i)) := borel _

local instance uniformWeilPlaceBorel (K L : Type u) [Field K] [Field L] [NumberField K]
    [Algebra K L] [FiniteDimensional K L] (n : ℕ) (i : Place K) :
    BorelSpace (GeneralLinear n (LocalBaseChangeAlgebra K L i)) := ⟨rfl⟩

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "Wₙ" => weilGroup K L GLₙ

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Under global matching and the simple trace comparison, one positive constant
compares the cuspidal traces of every pair of factorizable convolutions with locally
concordant factors and with the support and cuspidality conditions of the simple formulas. -/
def UniformConcordantConvolutionTraceStatement : Prop :=
  GeneralLinearBaseChangeGlobalMatchingStatement.{u} →
  GeneralLinearBaseChangeTraceComparisonStatement.{u} →
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (l : ℕ), IsCyclicAlgebra σ l →
    ∀ (n : ℕ) (hPD : ParabolicDynamicStatement.{u})
    (hG : IsConnectedReductive GLₙ) (hW : IsConnectedReductive Wₙ)
    (T₀ : CommGroupScheme (Spec (CommRingCat.of K)))
    (iG : T₀.toGrp ⟶ GLₙ) (hiG : Function.Injective (characterRestrict iG))
    [(characterRestrict iG).range.FiniteIndex]
    (iW : T₀.toGrp ⟶ Wₙ) (hiW : Function.Injective (characterRestrict iW))
    [(characterRestrict iW).range.FiniteIndex]
    (I : Type u) [Fintype I] (e₀ : T₀.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I)
    (hcG : IsCentral iG) (hcW : IsCentral iW)
    [(Measure.haar : Measure (normOneSubgroup K Wₙ)).IsMulRightInvariant]
    [(Measure.haar : Measure (normOneSubgroup K GLₙ)).IsMulRightInvariant],
    iW = iG ≫ AffineWeil.unit K L GLₙ →
    iW ≫ (unitGaloisAut K L GLₙ σ).asIso.hom = iW →
    ∀ (S : Finset (Place K)), (∀ w : Langlands.Global.InfinitePlace K, (Sum.inl w : Place K) ∈ S) →
    ∀ (μF : (i : Place K) → Measure (GeneralLinear n (placeCompletion K i)))
      (μE : (i : Place K) → Measure (GeneralLinear n (LocalBaseChangeAlgebra K L i))),
      (∀ i ∈ S, (μF i).IsHaarMeasure ∧ (μE i).IsHaarMeasure) →
      (∀ v : Langlands.Global.FinitePlace K, (Sum.inr v : Place K) ∉ S →
        ∀ (μFv : Measure (GeneralLinear n (placeCompletion K (.inr v))))
          (μEv : Measure (GeneralLinear n (LocalBaseChangeAlgebra K L (.inr v)))),
          μFv.IsHaarMeasure → μEv.IsHaarMeasure →
          μFv (Langlands.GeneralLinearGroup.integralSubgroup (Fin n)
            (show Subring (placeCompletion K (.inr v)) from
              (v.adicCompletionIntegers K).toSubring)) = 1 →
          μEv (Langlands.GeneralLinearGroup.integralSubgroup (Fin n)
            (localIntegers K L v)) = 1 →
          AreConcordant (localGalois K L σ (.inr v)) l μFv μEv
            ((Langlands.GeneralLinearGroup.integralSubgroup (Fin n) (localIntegers K L v) :
              Set (GeneralLinear n (LocalBaseChangeAlgebra K L (.inr v)))).indicator 1)
            ((Langlands.GeneralLinearGroup.integralSubgroup (Fin n)
              (show Subring (placeCompletion K (.inr v)) from
                (v.adicCompletionIntegers K).toSubring) :
              Set (GeneralLinear n (placeCompletion K (.inr v)))).indicator 1)) →
    let μW : Measure (AdelicGroupPoints K Wₙ) := Measure.haar
    let μG : Measure (AdelicGroupPoints K GLₙ) := Measure.haar
    let Θ := adelicAut K (unitGaloisAut K L GLₙ σ)
    let Γ := positiveRationalSubgroup K Wₙ T₀ iW
    let μQ := positiveRationalQuotientHaarMeasure K Wₙ T₀ iW
    let Φ : AdelicGroupPoints K Wₙ → AdelicGL L n := fun g =>
      GeneralLinearGroupPoints.adelicHomeomorph L n
        (AdelicGroupPoints.map L (AffineWeil.unitBaseChange K L GLₙ)
          (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of L))
          (GroupScheme.GeneralLinear.baseChangeIso (Fin n) (Spec.algebraMap K L)).hom
          (AdelicGaloisUnit.weilAdelicEquiv K L GLₙ g))
    let N : AdelicGroupPoints K Wₙ → AdelicGroupPoints K Wₙ := fun g =>
      ((List.range l).map fun k => adelicAut K (unitGaloisAut K L GLₙ σ ^ k) g).prod
    let SW := fullAEL2CuspidalSubmodule K Wₙ hPD hW T₀ iW hiW I e₀ hcW
    ∀ (hΘ : ∀ x, Θ x ∈ Γ ↔ x ∈ Γ)
      (hΘμ : MeasurePreserving (quotientAutomorphism Γ Θ hΘ).symm μQ μQ),
    let J := twistOperator Γ Θ hΘ μQ hΘμ
    ∃ c : ℝ, 0 < c ∧
    ∀ (φloc : (i : Place K) → GeneralLinear n (LocalBaseChangeAlgebra K L i) → ℂ)
      (floc : (i : Place K) → GeneralLinear n (placeCompletion K i) → ℂ),
      (∀ i ∈ S, Continuous (φloc i) ∧ HasCompactSupport (φloc i)) →
      (∀ i ∈ S, Continuous (floc i) ∧ HasCompactSupport (floc i)) →
      (∀ i ∈ S, AreConcordant (localGalois K L σ i) l (μF i) (μE i) (φloc i) (floc i)) →
    ∀ φ₁ φ₂ : C_c(AdelicGroupPoints K Wₙ, ℂ),
      (∀ h₁ : Integrable φ₁ μW, IsHilbertSchmidt
        (fullAEL2CuspidalIntegratedAction K Wₙ hPD hW T₀ iW hiW I e₀ hcW μW φ₁ h₁)) →
      (∀ h₂ : Integrable φ₂ μW, IsHilbertSchmidt
        (fullAEL2CuspidalIntegratedAction K Wₙ hPD hW T₀ iW hiW I e₀ hcW μW φ₂ h₂)) →
      (∀ (P : ProperRationalParabolic Wₙ) (x y : AdelicGroupPoints K Wₙ),
        ∫ m, φ₂ (x * (m : AdelicGroupPoints K Wₙ) * y)
          ∂properParabolicHaarMeasure K Wₙ hPD hW P = 0) →
    let φ : AdelicGroupPoints K Wₙ → ℂ := fun g => ∫ a, φ₁ a * φ₂ (a⁻¹ * g) ∂μW
    ∀ w : Langlands.Global.FinitePlace L,
      (∀ g ∈ tsupport φ, IsRegularElliptic (FiniteAdelicGL.localProjection L n w
        (AdelicGL.finite L n (Φ (N g))))) →
    ∀ f₁ f₂ : C_c(AdelicGroupPoints K GLₙ, ℂ),
      (∀ h₁ : Integrable f₁ μG, IsHilbertSchmidt
        (fullAEL2CuspidalIntegratedAction K GLₙ hPD hG T₀ iG hiG I e₀ hcG μG f₁ h₁)) →
      (∀ h₂ : Integrable f₂ μG, IsHilbertSchmidt
        (fullAEL2CuspidalIntegratedAction K GLₙ hPD hG T₀ iG hiG I e₀ hcG μG f₂ h₂)) →
      (∀ (P : ProperRationalParabolic GLₙ) (x y : AdelicGroupPoints K GLₙ),
        ∫ m, f₂ (x * (m : AdelicGroupPoints K GLₙ) * y)
          ∂properParabolicHaarMeasure K GLₙ hPD hG P = 0) →
    let f : AdelicGroupPoints K GLₙ → ℂ := fun g => ∫ a, f₁ a * f₂ (a⁻¹ * g) ∂μG
    ∀ v : Langlands.Global.FinitePlace K,
      (∀ g ∈ tsupport f, IsRegularElliptic (FiniteAdelicGL.localProjection K n v
        (AdelicGL.finite K n (GeneralLinearGroupPoints.adelicHomeomorph K n g)))) →
      IsAdelicFactorization K S (fun i p => φloc i (localPointsEquiv K L n i p))
        (localIntegralFamily K L n) φ →
      IsAdelicFactorization K S (fun i p => floc i (localGLEquiv K n i p))
        (glIntegralFamily K n) f →
      ∃ (hφ : Integrable φ μW) (hf : Integrable f μG),
        let RW := haarQuotientL2IntegratedAction K Wₙ T₀ iW hiW I e₀ hcW μW φ hφ
        let RG := fullAEL2CuspidalIntegratedAction K GLₙ hPD hG T₀ iG hiG I e₀ hcG μG f hf
        operatorTrace (SW.orthogonalProjectionOnto ∘L (RW ∘L J) ∘L SW.subtypeL) =
          (c : ℂ) * operatorTrace RG

-- Resolve the group scheme instances before keeping their constructions opaque.
private abbrev weilCompressionTrace (K L : Type u) [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] (n : ℕ) :=
  cuspidalCompressionTraceOfConvolution K Wₙ

private abbrev glIntegratedTrace (K : Type u) [Field K] [NumberField K] (n : ℕ) :=
  cuspidalIntegratedTraceOfConvolution K GLₙ

-- Compare the parameters of the adelic constructions without unfolding their implementation.
attribute [local irreducible] Global.AdelicGroupPoints.normOneSubgroup
  Global.AdelicGroupPoints.rationalNormOneSubgroup
  AdelicGroupAutomorphism.normOneAut AdelicGroupAutomorphism.unitGaloisAut twistedCentralizer
  GroupScheme.AffineWeil.corepresentableBy GroupScheme.AffineWeil.tensorFunctor
  Global.AdelicGroupPoints.topologicalSpace

set_option allowUnsafeReducibility true in
attribute [local irreducible] AdelicGroupAutomorphism.weilGroup AffineWeil.groupScheme
  AffineWeil.unitBaseChange Corepresented.groupScheme

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 450000 in
set_option maxHeartbeats 2400000 in
set_option maxRecDepth 4000 in
theorem uniformConcordantConvolutionTrace : UniformConcordantConvolutionTraceStatement.{u} := by
  intro hMatch hCompare K _ _ L _ _ _ _ σ l hcyc n hPD hG hW T₀ iG hiG hIndexG iW hiW hIndexW
    I hI e₀ hcG hcW hHaarW hHaarG hUnit hFix S hInf μF μE hHaar hUnits μW μG Θ Γ μQ Φ N SW
    hΘ hΘμ J
  have hMatchAtPlaces := @hMatch K _ _ L _ _ _ _ σ l hcyc n T₀ iG hiG hIndexG iW hiW hIndexW
    I hI e₀ hcG hcW hHaarW hHaarG hUnit S hInf μF μE hHaar hUnits
  obtain ⟨c, hc, hMatchAtPlaces⟩ := hMatchAtPlaces
  refine ⟨c, hc, ?_⟩
  intro φloc floc hφloc hfloc hConcord φ₁ φ₂ hHSφ₁ hHSφ₂ hVanW φ w hEllW
    f₁ f₂ hHSf₁ hHSf₂ hVanG f v hEllG hFactorW hFactorG
  have hOrbital := hMatchAtPlaces φloc floc hφloc hfloc hConcord φ f hFactorW hFactorG w v
  have hCompareHere := @hCompare K _ _ L _ _ _ _ σ l hcyc n hPD hW T₀ iW hiW hIndexW
    I hI e₀ hcW hHaarW hFix hG T₀ iG hiG hIndexG I hI e₀ hcG hHaarG
  with_reducible
    have hCompareFactors := hCompareHere φ₁ φ₂
  with_reducible
    have hCompareUpper := hCompareFactors hHSφ₁ hHSφ₂ hVanW
  with_reducible
    have hCompareLower := hCompareUpper w hEllW f₁ f₂ hHSf₁ hHSf₂ hVanG
  with_reducible
    have hCompareTests := hCompareLower v hEllG
  have hNorm := hOrbital.1
  have hOffNorm := hOrbital.2
  have hTraceForScalar := hCompareTests (c : ℂ)
  with_reducible
    have hTraceAtNorms := hTraceForScalar hNorm
  with_reducible
    have hTrace := hTraceAtNorms hOffNorm
  obtain ⟨hΘ', hΘμ', hφ, hf, hTW, hTG, hTrace⟩ := hTrace
  refine ⟨hφ, hf, ?_⟩
  have hCompressW := @weilCompressionTrace K L _ _ _ _ _ n hPD hW T₀ iW hiW hIndexW I hI e₀
    hcW hHaarW φ₁ φ₂ hφ hVanW hTW J
  have hCompressG := @glIntegratedTrace K _ _ n hPD hG T₀ iG hiG hIndexG I hI e₀ hcG hHaarG
    f₁ f₂ hf hVanG hTG
  exact hCompressW.trans (hTrace.trans (congrArg (fun z : ℂ => (c : ℂ) * z) hCompressG.symm))

end Langlands.TraceFormula
