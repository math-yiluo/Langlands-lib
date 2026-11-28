import Langlands.TraceFormula.GeneralLinearDiscreteSeriesGlobalTest
import Langlands.TraceFormula.GlobalizationLocalIdentification
import Langlands.TraceFormula.CuspidalSummandTraceExtraction
import Langlands.TraceFormula.GeneralLinearLocalSelectionTestStatement
import Langlands.Automorphic.GeneralLinearCuspidalSummandRealizationProof
import Langlands.Automorphic.GeneralLinearFullAEL2CuspidalCompactnessProof
import Langlands.Automorphic.CuspidalAdmissible.Existence
import Langlands.Automorphic.CuspidalSlicePresentation
import Langlands.Automorphic.CuspidalPresentationUniverse
import Langlands.Automorphic.SupercuspidalComponent
import Langlands.Global.AdelicNormOneHaarRightInvariantProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex
import Langlands.GroupScheme.Rational.CharacterRestrictionInjective
import Langlands.GroupScheme.Rational.GeneralLinearCharacterAdapters

/-!
# Ordinary globalization of a square-integrable representation from local selection tests

See `GeneralLinearDiscreteSeriesGlobalizationReduction.md`.
-/

noncomputable section

set_option autoImplicit false

universe u uV uQ

open CategoryTheory AlgebraicGeometry MeasureTheory NumberField
open scoped CategoryTheory.MonObj

namespace Langlands.TraceFormula

open Langlands.Automorphic Langlands.Automorphic.GroupSchemeFunctions Langlands.Global
open Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.HarmonicAnalysis Langlands.Analysis.OperatorIdeals

attribute [local instance high] BaseChange.leftQuotientMeasurableSpace
attribute [local instance] BaseChange.leftQuotient_borelSpace

local instance dsReductionGLAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance dsReductionGLSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)
local instance dsReductionRationalGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Automorphic.RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance dsReductionContinuousGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Automorphic.ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance dsReductionSmoothGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Automorphic.FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance dsReductionFormsGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Automorphic.AutomorphicForms F n) := Submodule.addCommGroup _
local instance dsReductionStableGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Automorphic.StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance dsReductionLocalGroup {F : Type u} [Field F] [NumberField F] {n : ℕ}
    {v : Langlands.Global.FinitePlace F} (D : LocalRealization F n v) : AddCommGroup D.Space :=
  Submodule.addCommGroup _

/-- A presented local component whose matrix action is supercuspidal is a supercuspidal local
component. -/
theorem localRealization_isSupercuspidal_of_matrixAction {F : Type u} [Field F] [NumberField F]
    {r : ℕ} {v : Langlands.Global.FinitePlace F}
    (A : LocalRealization F (r + 1) v) (hi : A.IsIrreducible)
    (hA : GeneralLinear.IsSupercuspidal A.representation) : A.IsSupercuspidal := by
  let K := CompletionPadic.padicField v
  let A₀ := A.padicObject hi hA.1
  let : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
  let : TopologicalSpace (GeneralLinear (r + 1) K.Carrier) := K.canonicalGeneralLinearTopology (r + 1)
  have hsc : GeneralLinear.IsSupercuspidal A₀.obj.representation :=
    ⟨A.isAdmissible_canonical_iff.mpr hA.1, hA.2⟩
  let σ : GeneralLinear.SupercuspidalRep.{u, u} (F := K.Carrier) (n := r + 1) :=
    ⟨A₀.obj, hi, hsc⟩
  exact ⟨hi, hA.1, σ.isoClass, rfl⟩

/-- **Reduction of ordinary discrete-series globalization to local selection tests.** The
square-integrable selection test and the supercuspidal selection test imply
`GeneralLinearDiscreteSeriesGlobalizationStatement`. -/
def GeneralLinearDiscreteSeriesGlobalizationReductionStatement : Prop :=
  GeneralLinearDiscreteSeriesSelectionTestStatement.{u, uV, u} →
  GeneralLinearSupercuspidalSelectionTestStatement.{u, u} →
  GeneralLinearDiscreteSeriesGlobalizationStatement.{u, uV, uQ}

set_option maxRecDepth 4000 in
set_option maxHeartbeats 16000000 in
set_option backward.isDefEq.respectTransparency.types false in
theorem generalLinearDiscreteSeriesGlobalizationReduction :
    GeneralLinearDiscreteSeriesGlobalizationReductionStatement.{u, uV, uQ} := by
  intro hDS hSC K _ _ _ v₀ v₁ v₂ h01 h02 h12 r hr V _ _ ρ hρA hρI hρS
  classical
  let G := GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of K)
  let T := Gm (Spec (CommRingCat.of K))
  let i : T.toGrp ⟶ G := GroupScheme.GeneralLinear.scalarTorus (Fin (r + 1)) (CommRingCat.of K)
  have hG := GroupScheme.isConnectedReductive_generalLinear K (Fin (r + 1))
  let : Nonempty (Fin (r + 1)) := ⟨⟨0, Nat.succ_pos r⟩⟩
  have hs := GroupScheme.GeneralLinear.scalarTorus_isSplitComponent (n := Fin (r + 1)) K
  have hi : Function.Injective (characterRestrict i) :=
    characterRestrict_injective_of_centralSplitTorusCharacter centralSplitTorusCharacter hG hs
  let : (characterRestrict i).range.FiniteIndex := hs.finiteIndex_range_characterRestrict hG
  let : (Measure.haar : Measure (normOneSubgroup K G)).IsMulRightInvariant :=
    normOneHaarRightInvariant K G hG.smooth hG.connectedSpace
  let e := splitTorus.gmIso (Spec (CommRingCat.of K))
  have hc : IsCentral i := hs.isCentralSplitTorus.2
  have hPD : ParabolicDynamicStatement.{u} := parabolicDynamic
  have (v : Langlands.Global.FinitePlace K) :
      T2Space (GeneralLinear (r + 1) (FiniteCompletion K v)) := by
    let : ValuativeRel (v.adicCompletion K) := (CompletionPadic.topologicalData v).valuativeRel
    have : IsNonarchimedeanLocalField (v.adicCompletion K) :=
      (CompletionPadic.topologicalData v).localField
    exact LocalFieldTopology.generalLinear_t2Space (v.adicCompletion K) (r + 1)
  have (v : Langlands.Global.FinitePlace K) :
      LocallyCompactSpace (GeneralLinear (r + 1) (FiniteCompletion K v)) := by
    let : ValuativeRel (v.adicCompletion K) := (CompletionPadic.topologicalData v).valuativeRel
    have : IsNonarchimedeanLocalField (v.adicCompletion K) :=
      (CompletionPadic.topologicalData v).localField
    exact LocalFieldTopology.generalLinear_locallyCompactSpace (v.adicCompletion K) (r + 1)
  have (v : Langlands.Global.FinitePlace K) :
      TotallyDisconnectedSpace (GeneralLinear (r + 1) (FiniteCompletion K v)) := by
    let : ValuativeRel (v.adicCompletion K) := (CompletionPadic.topologicalData v).valuativeRel
    have : IsNonarchimedeanLocalField (v.adicCompletion K) :=
      (CompletionPadic.topologicalData v).localField
    exact LocalFieldTopology.generalLinear_totallyDisconnectedSpace (v.adicCompletion K) (r + 1)
  -- the local selection tests
  obtain ⟨φ₀, hsel₀, U₀, hU₀o, hU₀ne, hU₀⟩ := hDS K v₀ r V ρ hρA hρI hρS
  obtain ⟨φ₁, hcusp₁, hsel₁, U₁, hU₁o, hU₁ne, hU₁⟩ := hSC K v₁ r
  obtain ⟨φ₂, -, hsel₂, U₂, hU₂o, hU₂ne, hU₂⟩ := hSC K v₂ r
  let Φ : ∀ v : Langlands.Global.FinitePlace K, SchwartzBruhat (FiniteLocalGL K (r + 1) v) :=
    Function.update (Function.update (Function.update (fun _ => 0) v₂ φ₂) v₁ φ₁) v₀ φ₀
  have hΦ₀ : Φ v₀ = φ₀ := Function.update_self _ _ _
  have hΦ₁ : Φ v₁ = φ₁ :=
    (Function.update_of_ne h01.symm _ _).trans (Function.update_self _ _ _)
  have hΦ₂ : Φ v₂ = φ₂ :=
    ((Function.update_of_ne h02.symm _ _).trans (Function.update_of_ne h12.symm _ _)).trans
      (Function.update_self _ _ _)
  have hcuspΦ : BaseChange.HasVanishingConstantTerms (Φ v₁ : FiniteLocalGL K (r + 1) v₁ → ℂ) := by
    rw [hΦ₁]
    exact hcusp₁
  -- the global test
  obtain ⟨S, F, a, h0S, h1S, h2S, hF₀, hF₁, hF₂, hint, hTC, hcuspImg, hne⟩ :=
    exists_globalTest_trace_ne_zero K r hPD hG T i hi PUnit e hc v₀ v₁ v₂ h01 h02 h12 Φ
      hcuspΦ (by
        rintro v (rfl | rfl | rfl)
        · rw [hΦ₀]
          exact ⟨U₀, hU₀o, hU₀ne, hU₀⟩
        · rw [hΦ₁]
          exact ⟨U₁, hU₁o, hU₁ne, hU₁⟩
        · rw [hΦ₂]
          exact ⟨U₂, hU₂o, hU₂ne, hU₂⟩)
  -- a cuspidal summand with nonzero compressed trace
  obtain ⟨P, ⟨hPne, hPcl, hPinv, hPirr⟩, hPc, hRPtc, hRPne⟩ :=
    exists_irreducibleSummand_compressedTrace_ne_zero K G hPD hG T i hi PUnit e hc
      (generalLinearFullAEL2CuspidalCompactness K (r + 1) hPD hG T i hi PUnit e hc) Measure.haar _
      hint hTC hcuspImg hne
  let : CompleteSpace P := hPc
  obtain ⟨R, Φc, hΦc, hclosure⟩ := generalLinearCuspidalSummandRealization K r hPD T i hi PUnit e hc
    P ⟨hPne, hPcl, hPinv, hPirr⟩
  have hΦP : LinearMap.range Φc ≤ P := hclosure ▸ Submodule.le_topologicalClosure _
  obtain ⟨Bs, hBi, hBa⟩ := cuspidalIrreducibleAdmissibleFiniteSliceExistence K r R
  obtain ⟨D₀, hD₀⟩ := R.exists_presentation_of_finiteSlice Bs hBi hBa
  obtain ⟨D, hD⟩ := D₀.exists_small.{u, u, uQ} hD₀
  have hR := GlobalizationIdentification.hasUnitaryCentralCharacter_of_formClass K r hPD T i hi
    PUnit e hc R Φc hΦc
  -- transfer of the compressed trace to rewritten forms of the test
  have htransfer : ∀ (f' : AdelicGroupPoints K G → ℂ)
      (_hf' : f' = GlobalizationTensor.fullTest K (r + 1) S F a)
      (hint' : Integrable f' (Measure.haar : Measure (AdelicGroupPoints K G))),
      IsTraceClass (E := (P : Submodule ℂ (fullAEL2CuspidalSubmodule K G hPD hG T i hi PUnit e hc)))
        (P.orthogonalProjectionOnto ∘L
          fullAEL2CuspidalIntegratedAction K G hPD hG T i hi PUnit e hc Measure.haar f' hint' ∘L
            P.subtypeL : P →L[ℂ] P) ∧
      operatorTrace (E := (P : Submodule ℂ (fullAEL2CuspidalSubmodule K G hPD hG T i hi PUnit e hc)))
        (P.orthogonalProjectionOnto ∘L
          fullAEL2CuspidalIntegratedAction K G hPD hG T i hi PUnit e hc Measure.haar f' hint' ∘L
            P.subtypeL : P →L[ℂ] P) ≠ 0 := by
    rintro f' rfl hint'
    exact ⟨hRPtc, hRPne⟩
  let s (v : Langlands.Global.FinitePlace K) (y : PlaceGroupPoints K G (.inr v)) : ℂ :=
    F v (localMatrixHomeomorph K (r + 1) v y)
  let w := GlobalizationTensor.fullTestExterior K (r + 1) S F a v₀ v₁ v₂
  have hfull := GlobalizationTensor.fullTest_eq_threePlaceTensor K (r + 1) S F a v₀ v₁ v₂ h0S h1S h2S
    h01 h02 h12
  have hw (v : Langlands.Global.FinitePlace K) (hv : v = v₀ ∨ v = v₁ ∨ v = v₂) (hvS : v ∈ S)
      (z : AdelicGroupPoints K G) (x : PlaceGroupPoints K G (.inr v)) :
      w (z * ofPlace K G (.inr v) x) = w z := by
    rw [← GlobalizationTensor.finitePlacePointInclusion_eq_ofPlace K (r + 1) v x]
    exact GlobalizationTensor.fullTestExterior_mul_finitePlacePointInclusion K (r + 1) S F a
      v₀ v₁ v₂ v hvS hv z x
  have hat {v v' : Langlands.Global.FinitePlace K} (h : v' ≠ v) (z : AdelicGroupPoints K G)
      (x : PlaceGroupPoints K G (.inr v)) :
      atPlace K G (.inr v') (z * ofPlace K G (.inr v) x) = atPlace K G (.inr v') z := by
    rw [← GlobalizationTensor.finitePlacePointInclusion_eq_ofPlace K (r + 1) v x]
    exact atPlace_mul_finitePlacePointInclusion_of_ne K G h z x
  let : ∀ v : Langlands.Global.FinitePlace K,
      MeasurableSpace (GeneralLinear (r + 1) (v.adicCompletion K)) := fun _ => borel _
  have : ∀ v : Langlands.Global.FinitePlace K,
      BorelSpace (GeneralLinear (r + 1) (v.adicCompletion K)) := fun _ => ⟨rfl⟩
  -- the place v₀
  let fw₀ : AdelicGroupPoints K G → ℂ := fun x =>
    s v₁ (atPlace K G (.inr v₁) x) * (s v₂ (atPlace K G (.inr v₂) x) * w x)
  have hfw₀ : ∀ g x, fw₀ (g * ofPlace K G (.inr v₀) x) = fw₀ g := by
    intro g x
    simp only [fw₀, hat h01.symm, hat h02.symm, hw v₀ (Or.inl rfl) h0S]
  have heq₀ : (fun g => F v₀ (localMatrixHomeomorph K (r + 1) v₀ (atPlace K G (.inr v₀) g)) * fw₀ g) =
      GlobalizationTensor.fullTest K (r + 1) S F a := by
    rw [hfull]
    rfl
  have hint₀ : Integrable (fun g => F v₀ (localMatrixHomeomorph K (r + 1) v₀
      (atPlace K G (.inr v₀) g)) * fw₀ g) (Measure.haar : Measure (AdelicGroupPoints K G)) := by
    rw [heq₀]
    exact hint
  obtain ⟨htc₀, hne₀⟩ := htransfer _ heq₀ hint₀
  obtain ⟨μ₀, hμ₀, hdist₀⟩ := GlobalizationIdentification.exists_distribution_ne_zero_of_compressedTrace
    K r hPD T i hi PUnit e hc P hPinv hPirr R Φc hΦc hΦP D v₀ (hD v₀).1 (hD v₀).2 (F v₀) fw₀ hfw₀
    hint₀ htc₀ hne₀
  -- the place v₁
  let fw₁ : AdelicGroupPoints K G → ℂ := fun x =>
    s v₀ (atPlace K G (.inr v₀) x) * (s v₂ (atPlace K G (.inr v₂) x) * w x)
  have hfw₁ : ∀ g x, fw₁ (g * ofPlace K G (.inr v₁) x) = fw₁ g := by
    intro g x
    simp only [fw₁, hat h01, hat h12.symm, hw v₁ (Or.inr (Or.inl rfl)) h1S]
  have heq₁ : (fun g => F v₁ (localMatrixHomeomorph K (r + 1) v₁ (atPlace K G (.inr v₁) g)) * fw₁ g) =
      GlobalizationTensor.fullTest K (r + 1) S F a := by
    rw [hfull]
    funext x
    simp only [fw₁, s, threePlaceTensor]
    ring
  have hint₁ : Integrable (fun g => F v₁ (localMatrixHomeomorph K (r + 1) v₁
      (atPlace K G (.inr v₁) g)) * fw₁ g) (Measure.haar : Measure (AdelicGroupPoints K G)) := by
    rw [heq₁]
    exact hint
  obtain ⟨htc₁, hne₁⟩ := htransfer _ heq₁ hint₁
  obtain ⟨μ₁, hμ₁, hdist₁⟩ := GlobalizationIdentification.exists_distribution_ne_zero_of_compressedTrace
    K r hPD T i hi PUnit e hc P hPinv hPirr R Φc hΦc hΦP D v₁ (hD v₁).1 (hD v₁).2 (F v₁) fw₁ hfw₁
    hint₁ htc₁ hne₁
  -- the place v₂
  let fw₂ : AdelicGroupPoints K G → ℂ := fun x =>
    s v₀ (atPlace K G (.inr v₀) x) * (s v₁ (atPlace K G (.inr v₁) x) * w x)
  have hfw₂ : ∀ g x, fw₂ (g * ofPlace K G (.inr v₂) x) = fw₂ g := by
    intro g x
    simp only [fw₂, hat h02, hat h12, hw v₂ (Or.inr (Or.inr rfl)) h2S]
  have heq₂ : (fun g => F v₂ (localMatrixHomeomorph K (r + 1) v₂ (atPlace K G (.inr v₂) g)) * fw₂ g) =
      GlobalizationTensor.fullTest K (r + 1) S F a := by
    rw [hfull]
    funext x
    simp only [fw₂, s, threePlaceTensor]
    ring
  have hint₂ : Integrable (fun g => F v₂ (localMatrixHomeomorph K (r + 1) v₂
      (atPlace K G (.inr v₂) g)) * fw₂ g) (Measure.haar : Measure (AdelicGroupPoints K G)) := by
    rw [heq₂]
    exact hint
  obtain ⟨htc₂, hne₂⟩ := htransfer _ heq₂ hint₂
  obtain ⟨μ₂, hμ₂, hdist₂⟩ := GlobalizationIdentification.exists_distribution_ne_zero_of_compressedTrace
    K r hPD T i hi PUnit e hc P hPinv hPirr R Φc hΦc hΦP D v₂ (hD v₂).1 (hD v₂).2 (F v₂) fw₂ hfw₂
    hint₂ htc₂ hne₂
  -- selection at the three places
  rw [hF₀, hΦ₀] at hdist₀
  rw [hF₁, hΦ₁] at hdist₁
  rw [hF₂, hΦ₂] at hdist₂
  have hunit : IsUnitarizable (D.localComponent v₀).representation :=
    cuspidalUnitaryLocalUnitarity K r R hR D v₀ (hD v₀).1 (hD v₀).2
  have hgen := D.exists_generic_at_completion hR v₀ (hD v₀).1 (hD v₀).2
  obtain ⟨χ, hχ₁, hχ₂, hχ₃⟩ := hsel₀ _ (D.localComponent v₀).representation (hD v₀).2 (hD v₀).1
    hunit hgen μ₀ hdist₀
  have hsc₁ := hsel₁ _ (D.localComponent v₁).representation (hD v₁).2 (hD v₁).1 μ₁ hdist₁
  have hsc₂ := hsel₂ _ (D.localComponent v₂).representation (hD v₂).2 (hD v₂).1 μ₂ hdist₂
  exact ⟨R, D, hR, hD, localRealization_isSupercuspidal_of_matrixAction _ (hD v₁).1 hsc₁,
    localRealization_isSupercuspidal_of_matrixAction _ (hD v₂).1 hsc₂, χ, hχ₁, hχ₂, hχ₃⟩

end Langlands.TraceFormula
