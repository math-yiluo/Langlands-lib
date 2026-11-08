import Langlands.Automorphic.CuspidalPresentationUniverse
import Langlands.Representation.Smooth.Factorization.RestrictedProductExistenceProof
import Langlands.Representation.Unramified.SphericalHeckeCommutativity
import Langlands.Global.FiniteAdelicGL.PadicComparison
import Langlands.Representation.CuspidalSupport.GroupTransport
import Langlands.Representation.CompactCoefficient.GroupTransport

/-! # Spectral presentations from irreducible admissible finite slices -/

noncomputable section
universe uF
set_option autoImplicit false

namespace Langlands.Global.FiniteAdelicGL

open MeasureTheory

variable {F : Type uF} [Field F] [NumberField F]

/-- Total disconnectedness of the canonical topology on the actual local group. -/
theorem canonical_totallyDisconnected (v : FinitePlace F) (n : ℕ) :
    letI := (CompletionPadic.padicField v).canonicalTopologicalData.topology
    TotallyDisconnectedSpace (GeneralLinear n (CompletionPadic.padicField v).Carrier) := by
  let T := (CompletionPadic.padicField v).canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let : NonarchimedeanRing (CompletionPadic.padicField v).Carrier := by
    convert! ValuativeRel.nonarchimedeanRing (CompletionPadic.padicField v).Carrier using 1
    exact Valuation.toTopologicalSpace_eq (ValuativeRel.valuation _)
  have : TotallyDisconnectedSpace (CompletionPadic.padicField v).Carrier := inferInstance
  have : TotallyDisconnectedSpace
      (Matrix (Fin n) (Fin n) (CompletionPadic.padicField v).Carrier) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → _))
  exact ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn
    Units.val_injective (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

/-- The topological hypotheses of Flath's theorem for the completion topology. -/
theorem localGL_flathTopology (v : FinitePlace F) (r : ℕ) :
    T2Space (FiniteLocalGL F (r + 1) v) ∧ LocallyCompactSpace (FiniteLocalGL F (r + 1) v) ∧
      TotallyDisconnectedSpace (FiniteLocalGL F (r + 1) v) ∧
      IsCompact (localIntegral F (r + 1) v : Set (FiniteLocalGL F (r + 1) v)) := by
  have hset : (localIntegral F (r + 1) v : Set (FiniteLocalGL F (r + 1) v)) =
      (Correspondence.sphericalSubgroup (CompletionPadic.padicField v) r :
        Set (FiniteLocalGL F (r + 1) v)) := by
    ext g
    change g ∈ (localIntegral F (r + 1) v).toSubgroup ↔
      g ∈ Correspondence.sphericalSubgroup (CompletionPadic.padicField v) r
    rw [localIntegral_eq_sphericalSubgroup F v r]
  rw [hset]
  have key : ∀ τ : TopologicalSpace (FiniteLocalGL F (r + 1) v),
      τ = (CompletionPadic.padicField v).canonicalGeneralLinearTopology (r + 1) →
      @T2Space _ τ ∧ @LocallyCompactSpace _ τ ∧ @TotallyDisconnectedSpace _ τ ∧
        @IsCompact _ τ (Correspondence.sphericalSubgroup (CompletionPadic.padicField v) r :
          Set (FiniteLocalGL F (r + 1) v)) := by
    intro τ hτ
    subst hτ
    exact ⟨(CompletionPadic.padicField v).canonicalGeneralLinearT2Space (r + 1),
      (CompletionPadic.padicField v).canonicalGeneralLinearLocallyCompactSpace (r + 1),
      canonical_totallyDisconnected v (r + 1),
      Unramified.sphericalOpenSubgroup_isCompact (CompletionPadic.padicField v) r⟩
  exact key _ (localGL_topology_eq F v (r + 1))

/-- A regular Haar measure on the actual local group whose spherical Hecke algebra at
the integral subgroup is commutative. -/
theorem localGL_exists_sphericalHeckeCommutative (v : FinitePlace F) (r : ℕ) :
    letI : MeasurableSpace (FiniteLocalGL F (r + 1) v) := borel _
    haveI : BorelSpace (FiniteLocalGL F (r + 1) v) := ⟨rfl⟩
    ∃ μ : Measure (FiniteLocalGL F (r + 1) v), μ.IsHaarMeasure ∧ μ.Regular ∧
      SphericalHeckeCommutative μ (localIntegral F (r + 1) v).toSubgroup := by
  rw [localIntegral_eq_sphericalSubgroup F v r]
  have key : ∀ (τ : TopologicalSpace (FiniteLocalGL F (r + 1) v))
      (_ : @IsTopologicalGroup _ τ _),
      τ = (CompletionPadic.padicField v).canonicalGeneralLinearTopology (r + 1) →
      letI : MeasurableSpace (FiniteLocalGL F (r + 1) v) := borel _
      haveI : BorelSpace (FiniteLocalGL F (r + 1) v) := ⟨rfl⟩
      ∃ μ : Measure (FiniteLocalGL F (r + 1) v), μ.IsHaarMeasure ∧ μ.Regular ∧
        SphericalHeckeCommutative μ
          (Correspondence.sphericalSubgroup (CompletionPadic.padicField v) r) := by
    intro τ _ hτ
    subst hτ
    let : TopologicalSpace (FiniteLocalGL F (r + 1) v) :=
      (CompletionPadic.padicField v).canonicalGeneralLinearTopology (r + 1)
    let : MeasurableSpace (FiniteLocalGL F (r + 1) v) := borel _
    have : BorelSpace (FiniteLocalGL F (r + 1) v) := ⟨rfl⟩
    have := (CompletionPadic.padicField v).canonicalGeneralLinearLocallyCompactSpace (r + 1)
    have := (CompletionPadic.padicField v).canonicalGeneralLinearT2Space (r + 1)
    refine ⟨Unramified.sphericalHaar (CompletionPadic.padicField v) r,
      Unramified.sphericalHaar_isHaar _ r,
      RankinSelberg.normalizedCompactOpenHaar_regular _ _, ?_⟩
    intro f g hf hg
    exact congrArg Subtype.val
      (Unramified.sphericalHeckeAlgebra_mul_comm (CompletionPadic.padicField v) r ⟨f, hf⟩ ⟨g, hg⟩)
  exact key _ inferInstance (localGL_topology_eq F v (r + 1))

end Langlands.Global.FiniteAdelicGL

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor MeasureTheory

variable {F : Type uF} [Field F] [NumberField F]

local instance slicePresentationGroup1 (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance slicePresentationGroup2 (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance slicePresentationGroup3 (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance slicePresentationGroup4 (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance slicePresentationGroup5 (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance slicePresentationGroup6 (n : ℕ) (S : FiniteRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

set_option maxHeartbeats 4000000 in
/-- **Flath assembly.** An irreducible admissible actual finite slice of a cuspidal
realization carries a complete spectral presentation, with factors in the form-space
universe, whose actual local components are irreducible and admissible at every place. -/
theorem CuspidalOperatorRealization.exists_presentation_of_finiteSlice
    [CompactSpace (AdeleQuotient F)] {r : ℕ} (S : CuspidalOperatorRealization F r)
    (A : S.FiniteSlice) (hI : A.subspace.IsIrreducible)
    (hA : Langlands.IsAdmissible A.subspace.representation) :
    ∃ P : CuspidalSpectralPresentation.{uF, uF} S,
      ∀ v, (P.localComponent v).IsIrreducible ∧ (P.localComponent v).IsAdmissible := by
  classical
  have htop := fun v => localGL_flathTopology (F := F) v r
  have : ∀ v, T2Space (FiniteLocalGL F (r + 1) v) := fun v => (htop v).1
  have : ∀ v, LocallyCompactSpace (FiniteLocalGL F (r + 1) v) := fun v => (htop v).2.1
  have : ∀ v, TotallyDisconnectedSpace (FiniteLocalGL F (r + 1) v) := fun v => (htop v).2.2.1
  let : ∀ v, MeasurableSpace (FiniteLocalGL F (r + 1) v) := fun v => borel _
  have : ∀ v, BorelSpace (FiniteLocalGL F (r + 1) v) := fun v => ⟨rfl⟩
  choose μ hμH hμR hμC using fun v => localGL_exists_sphericalHeckeCommutative (F := F) v r
  have : ∀ v, (μ v).IsHaarMeasure := hμH
  have : ∀ v, (μ v).Regular := hμR
  let H : ∀ v, Subgroup (FiniteLocalGL F (r + 1) v) :=
    fun v => (localIntegral F (r + 1) v).toSubgroup
  let π : Representation ℂ (RestrictedGroup (fun v => FiniteLocalGL F (r + 1) v) H)
      A.subspace.Space :=
    A.subspace.representation.comp (restrictedProductEquiv F (r + 1)).symm.toMonoidHom
  have hπA : IsAdmissible π :=
    isAdmissible_comp_continuousMulEquiv _ (restrictedProductEquiv F (r + 1)).symm hA
  have hπI : π.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff _ (restrictedProductEquiv F (r + 1)).symm).mpr hI
  obtain ⟨W, ρ, hρ, E, rr, hr, -, ⟨eq⟩⟩ := flathRestrictedProductExistence (FinitePlace F)
    (fun v => FiniteLocalGL F (r + 1) v) μ H A.subspace.Space π
    (fun v => ⟨(localIntegral F (r + 1) v).isOpen, (htop v).2.2.2⟩)
    (Filter.Eventually.of_forall hμC) hπA hπI
  let σ : ∀ v, Langlands.SmoothRep.{0, uF, uF} ℂ (FiniteLocalGL F (r + 1) v) :=
    fun v => Langlands.SmoothRep.of (ρ v) (hρ v).1.1
  have hfix : ∀ v ∉ E, ∀ g ∈ localIntegral F (r + 1) v,
      (σ v).representation g (rr.family v) = rr.family v := by
    intro v hv g hg
    rw [ReferenceVectors.family_of_not_mem rr hv]
    exact hr v hv g hg
  let e' : (tensorRepresentation F (r + 1) (fun v => (σ v).representation) E
      (fun v => rr.family v) hfix).Equiv A.subspace.representation :=
    Representation.Equiv.mk eq.symm.toLinearEquiv (fun g => by
      apply LinearMap.ext
      intro x
      have h := Representation.IntertwiningMap.isIntertwining _ _ eq.symm.toIntertwiningMap
        (restrictedProductEquiv F (r + 1) g) x
      refine h.trans ?_
      change A.subspace.representation ((restrictedProductEquiv F (r + 1)).symm
        (restrictedProductEquiv F (r + 1) g)) _ = _
      rw [ContinuousMulEquiv.symm_apply_apply]
      rfl)
  let pres : FiniteTensorPresentation F (r + 1) (fun v => (σ v).representation) E
      (fun v => rr.family v) hfix A.subspace :=
    { reference_nonzero := fun v hv => by
        rw [ReferenceVectors.family_of_not_mem rr hv]
        exact rr.nonzero v hv
      equiv := e' }
  let P : CuspidalSpectralPresentation.{uF, uF} S :=
    { finiteSlice := A
      localFactor := σ
      tensorExceptional := E
      reference := fun v => rr.family v
      reference_fixed := hfix
      presentation := pres
      exceptional := E
      unramified := pres.unramifiedData A.nonzero E (fun _ h => h)
        (fun v _ => (hρ v).2) (fun v _ => (hρ v).1) }
  exact ⟨P, fun v => ⟨(pres.localComponent_isIrreducible_iff A.nonzero v).mpr (hρ v).2,
    (pres.localComponent_isAdmissible_iff A.nonzero v).mpr (hρ v).1⟩⟩

set_option maxHeartbeats 1000000 in
/-- A chosen spectral presentation built from an irreducible admissible actual finite slice. -/
noncomputable def CuspidalOperatorRealization.slicePresentation
    [CompactSpace (AdeleQuotient F)] {r : ℕ} (S : CuspidalOperatorRealization F r)
    (A : S.FiniteSlice) (hI : A.subspace.IsIrreducible)
    (hA : Langlands.IsAdmissible A.subspace.representation) :
    CuspidalSpectralPresentation.{uF, uF} S :=
  Classical.choose (S.exists_presentation_of_finiteSlice A hI hA)

set_option maxHeartbeats 1000000 in
theorem CuspidalOperatorRealization.slicePresentation_localComponent
    [CompactSpace (AdeleQuotient F)] {r : ℕ} (S : CuspidalOperatorRealization F r)
    (A : S.FiniteSlice) (hI : A.subspace.IsIrreducible)
    (hA : Langlands.IsAdmissible A.subspace.representation) (v : FinitePlace F) :
    ((S.slicePresentation A hI hA).localComponent v).IsIrreducible ∧
      ((S.slicePresentation A hI hA).localComponent v).IsAdmissible := by
  unfold CuspidalOperatorRealization.slicePresentation
  exact Classical.choose_spec (S.exists_presentation_of_finiteSlice A hI hA) v

end Langlands.Automorphic
