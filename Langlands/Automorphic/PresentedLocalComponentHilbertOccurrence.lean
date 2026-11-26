import Langlands.Automorphic.AssociatedPresentationComparison
import Langlands.Automorphic.GeneralLinearQuotientFormClassClosure
import Langlands.Automorphic.RealizationSummandClassMap
import Langlands.Global.GeneralLinearLocalInclusionComparison
import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.TraceFormula.GeneralLinearCuspidalLocalComponentTraceStatement
import Langlands.TraceFormula.IsotypicTrace.CuspidalOccurrenceReduction

/-! # Occurrence of a presented finite component in its cuspidal Hilbert summand -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uQ uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Global Global.AdelicGroupPoints Global.PositiveRealTorus GroupScheme TraceFormula

local instance localOccurrenceGLAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance localOccurrenceGLSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)
local instance localOccurrenceRationalGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Automorphic.RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance localOccurrenceContinuousGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Automorphic.ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance localOccurrenceSmoothGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Automorphic.FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance localOccurrenceFormsGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Automorphic.AutomorphicForms F n) := Submodule.addCommGroup _
local instance localOccurrenceStableGroup (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Automorphic.StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance localOccurrenceLocalGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} {v : FinitePlace F}
    (D : LocalRealization F n v) : AddCommGroup D.Space := Submodule.addCommGroup _

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
  (hPD : ParabolicDynamicStatement.{u})
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]

local notation "G" => GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)
local notation "hG" => GroupScheme.isConnectedReductive_generalLinear F (Fin (r + 1))
local notation "S" => fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
local notation "πc" => fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc
local notation "μQ" => positiveRationalQuotientHaarMeasure F G T i

set_option maxHeartbeats 2000000 in
/-- A presented irreducible finite component embeds in the Hilbert summand
to which its form realization maps by the quotient class map. -/
def PresentedLocalComponentHilbertOccurrenceStatement : Prop :=
  ∀ (P : Submodule ℂ S) (R : CuspidalOperatorRealization F r) (Φ : R.Space →ₗ[ℂ] S),
    (∀ f, IsGeneralLinearFormClass F r T i (Φ f) (R.realization.toContinuous f)) →
    LinearMap.range Φ ≤ P →
    ∀ (D : CuspidalSpectralPresentation.{u, uQ} R) (v : FinitePlace F),
      (D.localComponent v).IsIrreducible →
      ∃ j : (D.localComponent v).Space →ₗ[ℂ] S, j ≠ 0 ∧ LinearMap.range j ≤ P ∧
        ∀ y x, j (localRealizationPlaceRepresentation (D.localComponent v) y x) =
          πc (ofPlace F G (.inr v) y) (j x)

set_option maxHeartbeats 4000000 in
theorem presentedLocalComponentHilbertOccurrence :
    PresentedLocalComponentHilbertOccurrenceStatement.{u, uQ} F r hPD T i hi I e hc := by
  intro P R Φ hΦ hP D v hI
  let A := D.localComponent v
  let a := R.realization.localSubspaceInclusion v A (D.localComponent_le_full v)
  let j := Φ.comp a.toLinearMap
  let hdesc : RealizationSummand.HasPositiveDescent F r T i R := fun f =>
    ⟨(hΦ f).choose, (hΦ f).choose_spec.1⟩
  let c := RealizationSummand.classMap F r T i R hdesc hi I e hc hPD
  have hcΦ (f : R.Space) : Φ f = c f := by
    apply Subtype.ext
    exact (hΦ f).unique
      (RealizationSummand.isGeneralLinearFormClass_classMap F r T i R hdesc hi I e hc hPD f)
  have hinj : Function.Injective Φ := by
    intro f g h
    apply RealizationSummand.classMap_injective F r T i R hdesc hi I e hc hPD
    exact (hcΦ f).symm.trans (h.trans (hcΦ g))
  have hja : Function.Injective j :=
    hinj.comp (R.realization.localSubspaceInclusion_injective v A (D.localComponent_le_full v))
  let : A.representation.IsIrreducible := hI
  have : Nontrivial A.representation.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (FiniteLocalGL F (r + 1) v)) A.representation.asModule
  have : Nontrivial A.Space := A.representation.asModuleEquiv.symm.toEquiv.nontrivial
  obtain ⟨x, hx⟩ := exists_ne (0 : A.Space)
  refine ⟨j, fun h => hx (hja (by rw [h]; rfl)), ?_, ?_⟩
  · rintro _ ⟨f, rfl⟩
    exact hP ⟨a f, rfl⟩
  · intro y f
    let g := localGLHomeomorph F (r + 1) (.inr v) y
    let d := FiniteAdelicGL.localInclusion F (r + 1) v g
    let h := ofPlace F G (.inr v) y
    have ha : a (A.representation g f) = R.realization.finiteRepresentation d (a f) :=
      Representation.IntertwiningMap.isIntertwining A.representation
        (R.realization.localRepresentation v) a g f
    have hd : (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm (AdelicGL.ofFinite F (r + 1) d) = h := by
      rw [← GeneralLinearGroupPoints.adelicHomeomorph_ofPlace F (r + 1) v y]
      exact ContinuousMulEquiv.symm_apply_apply _ _
    change Φ (a (A.representation g f)) = πc h (Φ (a f))
    rw [ha]
    apply Subtype.ext
    have ht := generalLinear_formClass_finiteRepresentation F r T i hi I e hc R.realization
      ((S).subtype.comp Φ) hΦ d (a f)
    rw [fullAEL2CuspidalBoundedRightAction_apply]
    change _ = quotientL2RightAction F G T i μQ
      (haarQuotientMeasureRightInvariant F G T i hi I e hc) h (Φ (a f)).val
    simpa only [LinearMap.comp_apply, Submodule.subtype_apply, hd,
      haarQuotientL2BoundedRightAction_apply] using ht

set_option maxHeartbeats 4100000 in
/-- A supplied irreducible admissible local occurrence in an irreducible
cuspidal Hilbert summand is equivalent to the presented local component. -/
theorem presentedLocalComponentEquivOfHilbertOccurrence
    (P : Submodule ℂ S) [CompleteSpace P]
    (hPinv : ∀ a, ∀ x ∈ P, πc a x ∈ P)
    (hPirr : ∀ Q : Submodule ℂ S, Q ≤ P → IsClosed (Q : Set S) →
      (∀ a, ∀ x ∈ Q, πc a x ∈ Q) → Q = ⊥ ∨ Q = P)
    (R : CuspidalOperatorRealization F r) (Φ : R.Space →ₗ[ℂ] S)
    (hΦ : ∀ f, IsGeneralLinearFormClass F r T i (Φ f) (R.realization.toContinuous f))
    (hP : LinearMap.range Φ ≤ P)
    (D : CuspidalSpectralPresentation.{u, uQ} R) (v : FinitePlace F)
    (hI : (D.localComponent v).IsIrreducible)
    [MeasurableSpace (PlaceGroupPoints F G (.inr v))]
    [BorelSpace (PlaceGroupPoints F G (.inr v))]
    [LocallyCompactSpace (PlaceGroupPoints F G (.inr v))]
    [TotallyDisconnectedSpace (PlaceGroupPoints F G (.inr v))]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (PlaceGroupPoints F G (.inr v)) V)
    (hρ : IsAdmissible ρ) (hρI : ρ.IsIrreducible)
    (j₀ : V →ₗ[ℂ] S) (h₀ : j₀ ≠ 0) (h₀P : LinearMap.range j₀ ≤ P)
    (h₀e : ∀ y x, j₀ (ρ y x) = πc (ofPlace F G (.inr v) y) (j₀ x)) :
    Nonempty ((localRealizationPlaceRepresentation (D.localComponent v)).Equiv ρ) := by
  let A := D.localComponent v
  let a := localGLHomeomorph F (r + 1) (.inr v)
  let τ := localRealizationPlaceRepresentation A
  have htI : τ.IsIrreducible := (isIrreducible_comp_continuousMulEquiv_iff A.representation a).2 hI
  have hts : IsSmooth τ := isSmooth_comp a.toMonoidHom a.continuous A.isSmooth
  obtain ⟨j, hj, hjP, hjE⟩ := presentedLocalComponentHilbertOccurrence F r hPD T i hi I e hc P R Φ hΦ hP D v hI
  have hIso := (IsotypicTrace.cuspidalIsotypicTraceFactorization_of_occurrence F G v hPD hG T i hi I e hc
    Measure.haar Measure.haar P hPinv hPirr ρ hρ hρI j₀ h₀ h₀P h₀e).1
  obtain ⟨b, hb⟩ := hIso A.Space τ hts htI j hj hjP hjE
  exact ⟨Representation.Equiv.mk b (fun y => LinearMap.ext (hb y))⟩

end Langlands.Automorphic.GroupSchemeFunctions
