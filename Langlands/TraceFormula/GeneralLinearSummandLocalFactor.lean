import Langlands.Automorphic.CuspidalAdmissible.Existence
import Langlands.Automorphic.CuspidalSlicePresentation
import Langlands.Automorphic.CuspidalWhittaker.LocalFunctional
import Langlands.Automorphic.LocalWhittakerCharacterBridge
import Langlands.BaseChange.AutomorphicObjectFieldPullback
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof
import Langlands.TraceFormula.GeneralLinearCuspidalLocalComponentTraceStatement

/-! # The local factor of a cuspidal summand of `GL_n`, read over a given p-adic field -/

noncomputable section

set_option autoImplicit false

universe u uF

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Analysis.OperatorIdeals Langlands.QuotientIntegration
open Langlands.HarmonicAnalysis Langlands.BaseChange Langlands.Correspondence Langlands.Unramified

namespace Langlands.TraceFormula

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

private local instance {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearLocallyCompactSpace n

private local instance {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    TotallyDisconnectedSpace (GeneralLinear n F.Carrier) :=
  LocalFieldTopology.generalLinear_totallyDisconnectedSpace F.Carrier n

local instance summandLocalFactorIsAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance summandLocalFactorSmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

local instance summandLocalFactorRationalAddCommGroup (K : Type u) [Field K] [NumberField K]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions K n) :=
  Submodule.addCommGroup _

local instance summandLocalFactorContinuousAddCommGroup (K : Type u) [Field K] [NumberField K]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions K n) :=
  Submodule.addCommGroup _

local instance summandLocalFactorSmoothAddCommGroup (K : Type u) [Field K] [NumberField K]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions K n) :=
  Submodule.addCommGroup _

local instance summandLocalFactorFormsAddCommGroup (K : Type u) [Field K] [NumberField K]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.AutomorphicForms K n) :=
  Submodule.addCommGroup _

local instance summandLocalFactorLocalSpaceAddCommGroup {K : Type u} [Field K] [NumberField K]
    {n : ℕ} {v : Langlands.Global.FinitePlace K} (A : LocalRealization K n v) :
    AddCommGroup A.Space :=
  Submodule.addCommGroup _

set_option hygiene false in
local notation "GLₙ" => GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of K)

/-- The points of `GL_{r+1}` over the completion at `v`, identified with `GL_{r+1}` of a
given p-adic field through a bicontinuous isomorphism of the completion with that field. -/
def localPlaceFieldEquiv (K : Type u) [Field K] [NumberField K] (r : ℕ)
    (v : Langlands.Global.FinitePlace K) {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (eF : FiniteCompletion K v ≃+* F.Carrier) (heF : Continuous eF) (heF' : Continuous eF.symm) :
    PlaceGroupPoints K GLₙ (.inr v) ≃ₜ* GeneralLinear (r + 1) F.Carrier :=
  (localGLHomeomorph K (r + 1) (.inr v)).trans (generalLinearRingEquiv eF heF heF')

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- Every irreducible cuspidal summand of `GL_{r+1}` over a number field has, at a finite
place `v`, a generic irreducible admissible local factor over a p-adic field identified with
the completion. The traces of factorized tests split off its distribution character for
the spherical Haar measure. -/
def GeneralLinearSummandLocalFactorStatement : Prop :=
  GeneralLinearCuspidalSummandRealizationStatement.{u} →
  GeneralLinearCuspidalLocalComponentTraceStatement.{u, u} →
  ∀ (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)] (r : ℕ)
    (hPD : ParabolicDynamicStatement.{u})
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ GLₙ)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup K GLₙ)).IsMulRightInvariant]
    (v : Langlands.Global.FinitePlace K)
    [MeasurableSpace (PlaceGroupPoints K GLₙ (.inr v))]
    [BorelSpace (PlaceGroupPoints K GLₙ (.inr v))]
    [LocallyCompactSpace (PlaceGroupPoints K GLₙ (.inr v))]
    [TotallyDisconnectedSpace (PlaceGroupPoints K GLₙ (.inr v))]
    (ν : Measure (AdelicGroupPoints K GLₙ)) [ν.IsHaarMeasure]
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (eF : FiniteCompletion K v ≃+* F.Carrier) (heF : Continuous eF) (heF' : Continuous eF.symm),
    let hG := GroupScheme.isConnectedReductive_generalLinear K (Fin (r + 1))
    let S := fullAEL2CuspidalSubmodule K _ hPD hG T i hi I e hc
    let πc := fullAEL2CuspidalBoundedRightAction K _ hPD hG T i hi I e hc
    let κ := localPlaceFieldEquiv K r v F eF heF heF'
    ∀ (P : Submodule ℂ S) [CompleteSpace P], P ≠ ⊥ →
      (∀ a, ∀ x ∈ P, πc a x ∈ P) →
      (∀ Q : Submodule ℂ S, Q ≤ P → IsClosed (Q : Set S) →
        (∀ a, ∀ x ∈ Q, πc a x ∈ Q) → Q = ⊥ ∨ Q = P) →
      ∃ (A : AutomorphicObject.{uF, u} F r.succPNat) (C : (AdelicGroupPoints K GLₙ → ℂ) → ℂ),
        (∃ ψ : NontrivialAdditiveCharacter F, Whittaker.IsGeneric ψ r A.obj.representation) ∧
        ∀ (fv : SchwartzBruhat (GeneralLinear (r + 1) F.Carrier))
          (fw : AdelicGroupPoints K GLₙ → ℂ),
          (∀ g x, fw (g * ofPlace K _ (.inr v) x) = fw g) →
          ∀ hf : Integrable (fun g => fv (κ (atPlace K _ (.inr v) g)) * fw g) ν,
            let RPf : P →L[ℂ] P := P.orthogonalProjectionOnto ∘L
              fullAEL2CuspidalIntegratedAction K _ hPD hG T i hi I e hc ν _ hf ∘L P.subtypeL
            IsTraceClass (E := (P : Submodule ℂ S)) RPf →
              operatorTrace (E := (P : Submodule ℂ S)) RPf =
                Character.distribution (sphericalHaar F r) A.obj.representation
                  A.property.2 fv * C fw

section Completion

variable {K : Type u} [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)] {r : ℕ}
  {R : CuspidalOperatorRealization K r} (D : CuspidalSpectralPresentation.{u, u} R)
  (v : Langlands.Global.FinitePlace K)
  (hI : (D.localComponent v).IsIrreducible) (hA : (D.localComponent v).IsAdmissible)
  {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (eF : FiniteCompletion K v ≃+* F.Carrier) (heF : Continuous eF) (heF' : Continuous eF.symm)

include heF heF'

omit [CompactSpace (AdeleQuotient K)] heF in
private theorem completion_continuous_symm :
    @Continuous F.Carrier (FiniteCompletion K v) _
      (CompletionPadic.padicField v).canonicalTopologicalData.topology eF.symm := by
  rw [← CompletionPadic.completion_topology_eq v]
  exact heF'

omit [CompactSpace (AdeleQuotient K)] heF' in
private theorem completion_continuous :
    @Continuous (FiniteCompletion K v) F.Carrier
      (CompletionPadic.padicField v).canonicalTopologicalData.topology _ eF.symm.symm := by
  rw [← CompletionPadic.completion_topology_eq v]
  exact heF

/-- The local component at `v` of a spectral presentation, read over a p-adic field
identified with the completion. -/
def presentationFieldObject : AutomorphicObject.{uF, u} F r.succPNat :=
  fieldPullbackObject (D := CompletionPadic.padicField v) eF.symm
    (completion_continuous_symm v F eF heF') (completion_continuous v F eF heF)
    ((D.localComponent v).padicObject hI hA)

theorem presentationFieldObject_representation (g : GeneralLinear (r + 1) F.Carrier) :
    (presentationFieldObject D v hI hA F eF heF heF').obj.representation g =
      (D.localComponent v).representation
        (Matrix.GeneralLinearGroup.map eF.symm.toRingHom g) := rfl

/-- The local component of a cuspidal presentation stays generic over the given field. -/
theorem presentationFieldObject_isGeneric :
    ∃ ψ : NontrivialAdditiveCharacter F,
      Whittaker.IsGeneric ψ r (presentationFieldObject D v hI hA F eF heF heF').obj.representation := by
  obtain ⟨ψ0⟩ := padicUnitaryAdditiveCharacterExists (CompletionPadic.padicField v)
    (CompletionPadic.padicField v).canonicalTopologicalData
  have hne : CuspidalWhittaker.localCharacter K v ≠ 1 := by
    intro h
    obtain ⟨t, ht⟩ := CuspidalWhittaker.exists_localCharacter_ne_one K v
    exact ht (by rw [h, AddChar.one_apply])
  obtain ⟨ℓ, hℓ, heq⟩ := CuspidalWhittaker.exists_localWhittakerFunctional (D.localComponent v)
    (D.localComponent_isCuspidal v) (D.localComponent_ne_bot v)
  have hgen := (D.localComponent v).isGeneric_of_integerTrivial_character hI hA
    (CuspidalWhittaker.localCharacter K v) hne
    (fun _ hx => CuspidalWhittaker.localCharacter_eq_one K hx) ℓ hℓ heq ψ0
  have h := fieldPullbackObject_isGeneric (D := CompletionPadic.padicField v) eF.symm
    (completion_continuous_symm v F eF heF') (completion_continuous v F eF heF)
    ((D.localComponent v).padicObject hI hA) ψ0 hgen
  exact ⟨_, h⟩

end Completion

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
theorem generalLinearSummandLocalFactor :
    GeneralLinearSummandLocalFactorStatement.{u, uF} := by
  intro hReal hLocal K _ _ _ r hPD T i hi _ I _ e hc _ v _ _ _ _ ν _ p _ F eF heF heF'
    hG S πc κ P _ hP hInv hIrr
  have hClosed : IsClosed (P : Set S) :=
    (completeSpace_coe_iff_isComplete.mp inferInstance).isClosed
  obtain ⟨R, Φ, hΦ, hRange⟩ := hReal K r hPD T i hi I e hc P ⟨hP, hClosed, hInv, hIrr⟩
  obtain ⟨Sl, hSlI, hSlA⟩ := cuspidalIrreducibleAdmissibleFiniteSliceExistence K r R
  obtain ⟨D, hD⟩ := R.exists_presentation_of_finiteSlice Sl hSlI hSlA
  let μv : Measure (PlaceGroupPoints K GLₙ (.inr v)) := (sphericalHaar F r).map κ.symm
  have : μv.IsHaarMeasure := κ.symm.isHaarMeasure_map (sphericalHaar F r)
  obtain ⟨hρ, C, hC⟩ := hLocal K r hPD T i hi I e hc v μv ν P hP hInv hIrr R Φ hΦ hRange D
    (hD v).1 (hD v).2
  refine ⟨presentationFieldObject D v (hD v).1 (hD v).2 F eF heF heF', C,
    presentationFieldObject_isGeneric D v (hD v).1 (hD v).2 F eF heF heF', ?_⟩
  intro fv fw hfw hf RPf hTC
  let ρv := localRealizationPlaceRepresentation (D.localComponent v)
  let fv' : SchwartzBruhat (PlaceGroupPoints K GLₙ (.inr v)) :=
    Hecke.TestFunction.pullback κ.symm.symm.toHomeomorph fv
  have h1 := hC fv' fw hfw hf hTC
  refine h1.trans ?_
  congr 1
  have heρ := isAdmissible_comp_continuousMulEquiv ρv κ.symm hρ
  have h2 := distribution_comp_equiv κ.symm (sphericalHaar F r) ρv hρ heρ fv
  refine h2.symm.trans ?_
  have hκ (g : GeneralLinear (r + 1) F.Carrier) :
      localGLHomeomorph K (r + 1) (.inr v) (κ.symm g) =
        Matrix.GeneralLinearGroup.map eF.symm.toRingHom g := by
    change localGLHomeomorph K (r + 1) (.inr v)
      ((localGLHomeomorph K (r + 1) (.inr v)).symm
        ((generalLinearRingEquiv eF heF heF').symm g)) = _
    rw [ContinuousMulEquiv.apply_symm_apply]
    rfl
  exact DFunLike.congr_fun (Character.distribution_eq_of_equivariant (sphericalHaar F r)
    (presentationFieldObject D v (hD v).1 (hD v).2 F eF heF heF').obj.representation
    (presentationFieldObject D v (hD v).1 (hD v).2 F eF heF heF').property.2
    (ρv.comp κ.symm.toMonoidHom) heρ (LinearEquiv.refl ℂ _) (fun g w => by
      change (D.localComponent v).representation
          (Matrix.GeneralLinearGroup.map eF.symm.toRingHom g) w =
        (D.localComponent v).representation (localGLHomeomorph K (r + 1) (.inr v) (κ.symm g)) w
      rw [hκ])).symm fv

end Langlands.TraceFormula
