import Langlands.Automorphic.CuspidalAdmissible.Existence
import Langlands.Automorphic.CuspidalSlicePresentation
import Langlands.Automorphic.CuspidalWhittaker.LocalFunctional
import Langlands.Automorphic.LocalWhittakerCharacterBridge
import Langlands.BaseChange.AutomorphicObjectFieldPullback
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof
import Langlands.TraceFormula.LocalCyclicProductCoordinates
import Langlands.TraceFormula.WeilGeneralLinearCuspidalLocalTwistedTraceStatement

/-! # The twisted local factor of a cuspidal summand of `Res_{L/K} GL_n`, read over a field -/

noncomputable section

set_option autoImplicit false

universe u uF uE

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.Global Langlands.Global.AdelicFunctoriality
open scoped NumberField FiniteExtension TensorProduct

namespace Langlands.TraceFormula

section LocalAlgebra

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] (v : Langlands.Global.FinitePlace K)

local notation "Kᵥ" => v.adicCompletion K
local notation "Eᵥ" => LocalBaseChangeAlgebra K L (Sum.inr v)

private local instance : Algebra Kᵥ Eᵥ := LocalBaseChangeAlgebra.algebra K L (.inr v)

private local instance : IsModuleTopology Kᵥ Eᵥ :=
  LocalBaseChangeAlgebra.isModuleTopology K L (.inr v)

omit [FiniteDimensional K L] in
private theorem placeAbove_isModuleTopology (q : FinitePlacesAbove L v) :
    IsModuleTopology Kᵥ (q.1.adicCompletion L) := by
  let : NontriviallyNormedField Kᵥ := AdelicSpaceLocalFields.normedField (𝓞 K) K v
  let : FiniteDimensional Kᵥ (q.1.adicCompletion L) := FiniteExtension.local_finite v q.1
  let : ContinuousSMul Kᵥ (q.1.adicCompletion L) :=
    continuousSMul_of_algebraMap _ _ (FiniteExtension.continuous_completionMap v q.1)
  exact isModuleTopologyOfFiniteDimensional (𝕜 := Kᵥ) (E := q.1.adicCompletion L)

/-- The completed tensor comparison at a finite place, as an algebra isomorphism. -/
def localTensorEquiv : Eᵥ ≃ₐ[Kᵥ] ((q : FinitePlacesAbove L v) → q.1.adicCompletion L) :=
  AlgEquiv.ofBijective (finiteTensorMap (L := L) v) ((completedTensorComparison K L).1 v)

omit [FiniteDimensional K L] in
/-- If the local algebra at `v` is a domain, exactly one place of `L` lies above `v`. -/
theorem exists_unique_placeAbove_of_isDomain [IsDomain Eᵥ] :
    ∃ w : FinitePlacesAbove L v, ∀ w', w' = w := by
  classical
  let c := localTensorEquiv K L v
  have hne : Nonempty (FinitePlacesAbove L v) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : Subsingleton ((q : FinitePlacesAbove L v) → q.1.adicCompletion L) := inferInstance
    exact one_ne_zero (c.injective (Subsingleton.elim (c 1) (c 0)))
  obtain ⟨w⟩ := hne
  refine ⟨w, fun w' => ?_⟩
  by_contra hw
  let a : Eᵥ := c.symm (Pi.single w 1)
  let b : Eᵥ := c.symm (Pi.single w' 1)
  have ha : a ≠ 0 := by
    intro h
    have := congrArg (fun x => c x w) h
    simp [a] at this
  have hb : b ≠ 0 := by
    intro h
    have := congrArg (fun x => c x w') h
    simp [b] at this
  have hab : a * b = 0 := by
    apply c.injective
    rw [map_mul, map_zero]
    simp only [a, b, AlgEquiv.apply_symm_apply]
    ext q
    by_cases hq : q = w'
    · subst hq
      simp [hw]
    · simp [hq]
  exact mul_ne_zero ha hb hab

/-- The local algebra identified with the completion at the unique place above `v`. -/
def localPlaceAboveEquiv (w : FinitePlacesAbove L v) (hw : ∀ w', w' = w) :
    Eᵥ ≃ₐ[Kᵥ] w.1.adicCompletion L :=
  let : Unique (FinitePlacesAbove L v) := ⟨⟨w⟩, hw⟩
  AlgEquiv.ofBijective
    ((Pi.evalAlgHom Kᵥ (fun q : FinitePlacesAbove L v => q.1.adicCompletion L) w).comp
      (finiteTensorMap (L := L) v))
    ((Equiv.piUnique (fun q : FinitePlacesAbove L v => q.1.adicCompletion L)).bijective.comp
      ((completedTensorComparison K L).1 v))

omit [FiniteDimensional K L] in
theorem localPlaceAboveEquiv_apply (w : FinitePlacesAbove L v) (hw : ∀ w', w' = w) (x : Eᵥ) :
    localPlaceAboveEquiv K L v w hw x = finiteTensorMap (L := L) v x w := rfl

omit [FiniteDimensional K L] in
theorem continuous_localPlaceAboveEquiv (w : FinitePlacesAbove L v) (hw : ∀ w', w' = w) :
    Continuous (localPlaceAboveEquiv K L v w hw) := by
  let := placeAbove_isModuleTopology K L v w
  exact IsModuleTopology.continuous_of_linearMap (localPlaceAboveEquiv K L v w hw).toLinearMap

theorem continuous_localPlaceAboveEquiv_symm (w : FinitePlacesAbove L v) (hw : ∀ w', w' = w) :
    Continuous (localPlaceAboveEquiv K L v w hw).symm := by
  let := placeAbove_isModuleTopology K L v w
  exact IsModuleTopology.continuous_of_linearMap
    (localPlaceAboveEquiv K L v w hw).symm.toLinearMap

end LocalAlgebra

section Completion

open Langlands.Automorphic Langlands.BaseChange Langlands.Correspondence Langlands.HarmonicAnalysis
open Langlands.Unramified

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2

local instance weilSummandRationalAddCommGroup (L : Type u) [Field L] [NumberField L]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions L n) :=
  Submodule.addCommGroup _

local instance weilSummandContinuousAddCommGroup (L : Type u) [Field L] [NumberField L]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions L n) :=
  Submodule.addCommGroup _

local instance weilSummandSmoothAddCommGroup (L : Type u) [Field L] [NumberField L]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.FiniteSmoothRationalFunctions L n) :=
  Submodule.addCommGroup _

local instance weilSummandFormsAddCommGroup (L : Type u) [Field L] [NumberField L]
    (n : ℕ) : AddCommGroup (Langlands.Automorphic.AutomorphicForms L n) :=
  Submodule.addCommGroup _

local instance weilSummandLocalSpaceAddCommGroup {L : Type u} [Field L] [NumberField L]
    {n : ℕ} {q : Langlands.Global.FinitePlace L} (A : LocalRealization L n q) :
    AddCommGroup A.Space :=
  Submodule.addCommGroup _

private local instance weilSummandLocalAlgebra (K L : Type u) [Field K] [Field L] [NumberField K]
    [Algebra K L] (v : Langlands.Global.FinitePlace K) :
    Algebra (v.adicCompletion K) (LocalBaseChangeAlgebra K L (Sum.inr v)) :=
  LocalBaseChangeAlgebra.algebra K L (.inr v)

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [CompactSpace (AdeleQuotient L)] {r : ℕ}
  {R : CuspidalOperatorRealization L r} (D : CuspidalSpectralPresentation.{u, u} R)
  (v : Langlands.Global.FinitePlace K) (w : FinitePlacesAbove L v) (hw : ∀ w', w' = w)
  (hI : (D.localComponent w.1).IsIrreducible) (hA : (D.localComponent w.1).IsAdmissible)
  {p : ℕ} [Fact p.Prime] (E : PadicField.{uE} p)
  (eE : LocalBaseChangeAlgebra K L (.inr v) ≃+* E.Carrier) (heE : Continuous eE)
  (heE' : Continuous eE.symm)

/-- The given field identified with the completion of `L` at the unique place above `v`. -/
def fieldPlaceAboveEquiv : E.Carrier ≃+* w.1.adicCompletion L :=
  eE.symm.trans (localPlaceAboveEquiv K L v w hw).toRingEquiv

include heE' in
omit [CompactSpace (AdeleQuotient L)] [FiniteDimensional K L] in
private theorem fieldPlaceAboveEquiv_continuous :
    @Continuous E.Carrier (w.1.adicCompletion L) _
      (CompletionPadic.padicField w.1).canonicalTopologicalData.topology
      (fieldPlaceAboveEquiv v w hw E eE) := by
  rw [← CompletionPadic.completion_topology_eq w.1]
  exact (continuous_localPlaceAboveEquiv K L v w hw).comp heE'

include heE in
omit [CompactSpace (AdeleQuotient L)] in
private theorem fieldPlaceAboveEquiv_continuous_symm :
    @Continuous (w.1.adicCompletion L) E.Carrier
      (CompletionPadic.padicField w.1).canonicalTopologicalData.topology _
      (fieldPlaceAboveEquiv v w hw E eE).symm := by
  rw [← CompletionPadic.completion_topology_eq w.1]
  exact heE.comp (continuous_localPlaceAboveEquiv_symm K L v w hw)

/-- The local component at the place above `v` of a spectral presentation over `L`, read over
the given field. -/
def weilPresentationFieldObject : AutomorphicObject.{uE, u} E r.succPNat :=
  fieldPullbackObject (D := CompletionPadic.padicField w.1) (fieldPlaceAboveEquiv v w hw E eE)
    (fieldPlaceAboveEquiv_continuous v w hw E eE heE')
    (fieldPlaceAboveEquiv_continuous_symm v w hw E eE heE)
    ((D.localComponent w.1).padicObject hI hA)

theorem weilPresentationFieldObject_representation (g : GeneralLinear (r + 1) E.Carrier) :
    (weilPresentationFieldObject D v w hw hI hA E eE heE heE').obj.representation g =
      (D.localComponent w.1).representation
        (Matrix.GeneralLinearGroup.map (fieldPlaceAboveEquiv v w hw E eE).toRingHom g) := rfl

/-- The local component stays generic over the given field. -/
theorem weilPresentationFieldObject_isGeneric :
    ∃ ψ : NontrivialAdditiveCharacter E,
      Whittaker.IsGeneric ψ r
        (weilPresentationFieldObject D v w hw hI hA E eE heE heE').obj.representation := by
  obtain ⟨ψ0⟩ := padicUnitaryAdditiveCharacterExists (CompletionPadic.padicField w.1)
    (CompletionPadic.padicField w.1).canonicalTopologicalData
  have hne : CuspidalWhittaker.localCharacter L w.1 ≠ 1 := by
    intro h
    obtain ⟨t, ht⟩ := CuspidalWhittaker.exists_localCharacter_ne_one L w.1
    exact ht (by rw [h, AddChar.one_apply])
  obtain ⟨ℓ, hℓ, heq⟩ := CuspidalWhittaker.exists_localWhittakerFunctional
    (D.localComponent w.1) (D.localComponent_isCuspidal w.1) (D.localComponent_ne_bot w.1)
  have hgen := (D.localComponent w.1).isGeneric_of_integerTrivial_character hI hA
    (CuspidalWhittaker.localCharacter L w.1) hne
    (fun _ hx => CuspidalWhittaker.localCharacter_eq_one L hx) ℓ hℓ heq ψ0
  have h := fieldPullbackObject_isGeneric (D := CompletionPadic.padicField w.1)
    (fieldPlaceAboveEquiv v w hw E eE)
    (fieldPlaceAboveEquiv_continuous v w hw E eE heE')
    (fieldPlaceAboveEquiv_continuous_symm v w hw E eE heE)
    ((D.localComponent w.1).padicObject hI hA) ψ0 hgen
  exact ⟨_, h⟩

end Completion

section Summand

open Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Automorphic Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Analysis.OperatorIdeals Langlands.QuotientIntegration
open Langlands.BaseChange Langlands.Correspondence Langlands.HarmonicAnalysis Langlands.Unramified
open Langlands.TraceFormula.AdelicGroupAutomorphism

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

private local instance {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearLocallyCompactSpace n

private local instance {p : ℕ} [Fact p.Prime] (F : PadicField p) (n : ℕ) :
    TotallyDisconnectedSpace (GeneralLinear n F.Carrier) :=
  LocalFieldTopology.generalLinear_totallyDisconnectedSpace F.Carrier n

local instance weilSummandIsAffine (K : Type u) [Field K] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of K)

local instance weilSummandSmooth (K : Type u) [Field K] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of K)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of K)

set_option hygiene false in
local notation "GLᵣ" => GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of K)

set_option hygiene false in
local notation "Wᵣ" => weilGroup K L GLᵣ

private theorem twistedDistribution_congr_representation {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [T2Space G]
    [LocallyCompactSpace G] [TotallyDisconnectedSpace G] (m : Measure G)
    [IsFiniteMeasureOnCompacts m] [m.IsMulLeftInvariant]
    {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ ρ' : Representation ℂ G V}
    (h : ∀ g, ρ g = ρ' g) (hρ : Langlands.IsAdmissible ρ) (hρ' : Langlands.IsAdmissible ρ')
    (B : Module.End ℂ V) :
    twistedDistribution m ρ hρ B = twistedDistribution m ρ' hρ' B := by
  obtain rfl : ρ = ρ' := MonoidHom.ext h
  rfl

set_option maxHeartbeats 1000000 in
/-- On a twist-stable irreducible cuspidal summand of the Weil restriction of `GL_{r+1}`,
the traces of tests factored at a finite place whose local algebra is identified with a
p-adic field `E` split off a twisted distribution of a generic irreducible admissible
representation of `GL_{r+1}(E)`, for an intertwiner of the given Galois automorphism. -/
def WeilSummandLocalFactorStatement : Prop :=
  WeilGeneralLinearCuspidalSummandRealizationStatement.{u} →
  WeilGeneralLinearCuspidalLocalTwistedTraceStatement.{u, u} →
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [CompactSpace (AdeleQuotient L)]
    (σK : L ≃ₐ[K] L) (r : ℕ)
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive Wᵣ)
    (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ Wᵣ)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup K Wᵣ)).IsMulRightInvariant]
    (ν : Measure (AdelicGroupPoints K Wᵣ)) [ν.IsHaarMeasure]
    (v : Langlands.Global.FinitePlace K) {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (E : PadicField.{uE} p) [Algebra F.Carrier E.Carrier]
    (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier)
    (eE : LocalBaseChangeAlgebra K L (.inr v) ≃+* E.Carrier)
    (heE : Continuous eE) (heE' : Continuous eE.symm),
    (∀ a, eE (localGalois K L σK (.inr v) a) = σ (eE a)) →
    let S := fullAEL2CuspidalSubmodule K Wᵣ hPD hG T i hi I e hc
    let πc := fullAEL2CuspidalBoundedRightAction K Wᵣ hPD hG T i hi I e hc
    let Θ : AdelicGroupPoints K Wᵣ ≃ₜ* AdelicGroupPoints K Wᵣ :=
      adelicAut K (unitGaloisAut K L GLᵣ σK)
    let κ := generalLinearRingEquiv (n := r + 1) eE heE heE'
    let gv : AdelicGroupPoints K Wᵣ → GeneralLinear (r + 1) (LocalBaseChangeAlgebra K L (.inr v)) :=
      fun g => localPointsEquiv K L (r + 1) (.inr v) (atPlace K Wᵣ (.inr v) g)
    ∀ (P : Submodule ℂ S) [CompleteSpace P], P ≠ ⊥ →
      (∀ a, ∀ x ∈ P, πc a x ∈ P) →
      (∀ Q : Submodule ℂ S, Q ≤ P → IsClosed (Q : Set S) →
        (∀ a, ∀ x ∈ Q, πc a x ∈ Q) → Q = ⊥ ∨ Q = P) →
    ∀ (hΘ : ∀ x, Θ x ∈ positiveRationalSubgroup K Wᵣ T i ↔
        x ∈ positiveRationalSubgroup K Wᵣ T i)
      (hΘμ : MeasurePreserving
        (quotientAutomorphism (positiveRationalSubgroup K Wᵣ T i) Θ hΘ).symm
        (positiveRationalQuotientHaarMeasure K Wᵣ T i)
        (positiveRationalQuotientHaarMeasure K Wᵣ T i)),
      let IΘ := twistOperator (positiveRationalSubgroup K Wᵣ T i) Θ hΘ
        (positiveRationalQuotientHaarMeasure K Wᵣ T i) hΘμ
      (∀ x ∈ P, ∃ y ∈ P, (y : Lp ℂ 2 (positiveRationalQuotientHaarMeasure K Wᵣ T i)) =
        IΘ (x : Lp ℂ 2 (positiveRationalQuotientHaarMeasure K Wᵣ T i))) →
      ∃ (A : AutomorphicObject.{uE, u} E r.succPNat)
        (B : SigmaIntertwiner σ (r + 1) A.obj.representation)
        (C : (AdelicGroupPoints K Wᵣ → ℂ) → ℂ),
        (∃ ψ : NontrivialAdditiveCharacter E, Whittaker.IsGeneric ψ r A.obj.representation) ∧
        ∀ (fv : SchwartzBruhat (GeneralLinear (r + 1) E.Carrier))
          (fw : AdelicGroupPoints K Wᵣ → ℂ),
          (∀ g x, fw (g * ofPlace K Wᵣ (.inr v) x) = fw g) →
          ∀ hf : Integrable (fun g => fv (κ (gv g)) * fw g) ν,
            let Rf := haarQuotientL2IntegratedAction K Wᵣ T i hi I e hc ν _ hf
            let BP : P →L[ℂ] P := P.orthogonalProjectionOnto ∘L
              (S.orthogonalProjectionOnto ∘L (Rf ∘L IΘ) ∘L S.subtypeL) ∘L P.subtypeL
            IsTraceClass (E := (P : Submodule ℂ S)) BP →
              set_option backward.isDefEq.respectTransparency false in
              operatorTrace (E := (P : Submodule ℂ S)) BP =
                twistedDistribution (sphericalHaar E r) A.obj.representation A.property.2
                  B.toLinearMap fv * C fw

attribute [local instance] weilSummandLocalSpaceAddCommGroup

-- Keep the Weil group scheme opaque, so that unification compares its arguments.
set_option allowUnsafeReducibility true in
attribute [local irreducible] AdelicGroupAutomorphism.weilGroup AffineWeil.groupScheme
  AffineWeil.unitBaseChange Corepresented.groupScheme

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
theorem weilSummandLocalFactor : WeilSummandLocalFactorStatement.{u, uF, uE} := by
  intro hReal hLocal K _ _ L _ _ _ _ _ σK r hPD hG T i hi _ I _ e hc _ ν _ v p _ F E _ σ eE
    heE heE' hTwist S πc Θ κ gv P _ hP hInv hIrr hΘ hΘμ IΘ hPΘ
  have hClosed : IsClosed (P : Set S) :=
    (completeSpace_coe_iff_isComplete.mp inferInstance).isClosed
  obtain ⟨R, Ψ, hΨ, hRange⟩ := hReal K L r hPD hG T i hi I e hc P ⟨hP, hClosed, hInv, hIrr⟩
  obtain ⟨Sl, hSlI, hSlA⟩ := cuspidalIrreducibleAdmissibleFiniteSliceExistence L r R
  obtain ⟨D, hD⟩ := R.exists_presentation_of_finiteSlice Sl hSlI hSlA
  have : IsDomain (LocalBaseChangeAlgebra K L (.inr v)) :=
    Function.Injective.isDomain eE.toRingHom eE.injective
  obtain ⟨w, hw⟩ := exists_unique_placeAbove_of_isDomain K L v
  let : MeasurableSpace (GeneralLinear (r + 1) (LocalBaseChangeAlgebra K L (.inr v))) := borel _
  have : BorelSpace (GeneralLinear (r + 1) (LocalBaseChangeAlgebra K L (.inr v))) := ⟨rfl⟩
  have : T2Space (GeneralLinear (r + 1) (LocalBaseChangeAlgebra K L (.inr v))) :=
    κ.toHomeomorph.isEmbedding.t2Space
  have : LocallyCompactSpace (GeneralLinear (r + 1) (LocalBaseChangeAlgebra K L (.inr v))) :=
    κ.toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have : TotallyDisconnectedSpace (GeneralLinear (r + 1) (LocalBaseChangeAlgebra K L (.inr v))) :=
    ⟨isTotallyDisconnected_of_image κ.continuous.continuousOn κ.injective
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  let : TopologicalSpace (v.adicCompletion K ⊗[K] L) :=
    moduleTopology (v.adicCompletion K) (v.adicCompletion K ⊗[K] L)
  let : MeasurableSpace (GeneralLinear (r + 1) (v.adicCompletion K ⊗[K] L)) := borel _
  let μv : Measure (GeneralLinear (r + 1) (v.adicCompletion K ⊗[K] L)) :=
    (sphericalHaar E r).map κ.symm
  have hμv : μv.IsHaarMeasure := κ.symm.isHaarMeasure_map (sphericalHaar E r)
  have h3 := hLocal K L σK r hPD hG T i hi I e hc ν P hP hInv hIrr R Ψ hΨ hRange v w hw μv D
    (hD w.1).1 (hD w.1).2
  obtain ⟨hρ, -, h2⟩ := h3
  have h4 := h2 hΘ hΘμ hPΘ
  obtain ⟨A, C, hC⟩ := h4
  let Aw := weilPresentationFieldObject D v w hw (hD w.1).1 (hD w.1).2 E eE heE heE'
  have hσ : ∀ x, eE.symm (σ x) = localGalois K L σK (.inr v) (eE.symm x) := fun x => by
    apply eE.injective
    rw [hTwist, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  refine ⟨Aw, A.ringPullback eE.symm hσ (fun g => rfl), C,
    weilPresentationFieldObject_isGeneric D v w hw (hD w.1).1 (hD w.1).2 E eE heE heE', ?_⟩
  intro fv fw hfw hf Rf BP hTC
  refine (hC (Hecke.TestFunction.pullback κ.symm.symm.toHomeomorph fv) fw hfw hf hTC).trans ?_
  congr 1
  have heρ := isAdmissible_comp_continuousMulEquiv _ κ.symm hρ
  refine (twistedDistribution_comp_equiv κ.symm (sphericalHaar E r) _ hρ heρ
    A.toLinearMap fv).symm.trans ?_
  exact DFunLike.congr_fun (twistedDistribution_congr_representation (sphericalHaar E r)
    (ρ' := Aw.obj.representation) (fun g => rfl) heρ Aw.property.2 A.toLinearMap) fv

end Summand

end Langlands.TraceFormula
