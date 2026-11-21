import Langlands.Global.Factors.CuspidalNormPowerTwist
import Langlands.Automorphic.ContragredientUniqueness
import Langlands.Automorphic.CuspidalContragredientPresentationExistenceProof
import Langlands.Automorphic.CuspidalJointAdmissibility
import Langlands.Global.Factors.CuspidalCommonSplitCentreTwist
import Langlands.Global.Factors.CuspidalNondualPartialEulerContinuation
import Langlands.Global.Factors.CuspidalPairFiniteLayer
import Langlands.Global.Factors.CuspidalSelfPairEntireObstruction
import Langlands.Global.Factors.CuspidalSplitCentreUnitaryProof
import Langlands.Global.Factors.CuspidalStrongMultiplicityOneStatement
import Langlands.Global.RankinSelberg.SelfPairContragredient
import Langlands.Representation.Unramified.SphericalSpectrumUniquenessProof

/-! # Strong multiplicity one from the completed pair pole theorem -/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global

open NumberField Automorphic CuspidalPairPoles CuspidalPairFunctionalEquation
open CuspidalPairBoundaryNonvanishing CuspidalSelfPairAssembly
open Automorphic.ContinuousRationalFunctions (evaluate)
open Langlands.ClassField.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

/-- The completed cuspidal pair pole theorem implies strong multiplicity one. -/
def CuspidalStrongMultiplicityOneFromPairPole : Prop :=
  CuspidalPairPoleStatement.{u,uQ} → CuspidalStrongMultiplicityOneStatement.{u,uQ}

private theorem inverse_intertwines {V W : Type*} (e : V ≃ W) {L : V → V} {R : W → W}
    (h : ∀ x, R (e x) = e (L x)) (y : W) : L (e.symm y) = e.symm (R y) := by
  apply e.injective
  rw [← h, e.apply_symm_apply, e.apply_symm_apply]

section Realizations

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} {T T' : CuspidalOperatorRealization F r}

set_option maxHeartbeats 1200000 in
private theorem dual_conjugate (hT : HasUnitaryCentralCharacter T.conjugate) :
    T.realization.IsContragredientOf T.conjugate.realization := by
  obtain ⟨b⟩ := T.conjugate.isUnitarizable_of_hasUnitaryCentralCharacter hT
  let e := T.conjugateEquiv
  refine OperatorRealization.isContragredientOf_of_unitaryForm b T.conjugate.isJointlyAdmissible
    e.symm ?_ ?_ ?_
  · intro d
    exact inverse_intertwines e.toEquiv (T.conjugateEquiv_finite d)
  · intro k
    exact inverse_intertwines e.toEquiv (T.conjugateEquiv_compact k)
  · intro X
    exact inverse_intertwines e.toEquiv (T.conjugateEquiv_lieAction X)

set_option maxHeartbeats 1000000 in
private theorem eigenvalues_eq_of_localClass_eq
    (P : CuspidalSpectralPresentation.{u,uQ} T) (P' : CuspidalSpectralPresentation.{u,uQ} T')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (v : FinitePlace F) (hv : v ∉ P.exceptional) (hv' : v ∉ P'.exceptional)
    (heq : localClass P h v = localClass P' h' v) :
    P.spectralSystem.eigenvalues v hv = P'.spectralSystem.eigenvalues v hv' := by
  let K := CompletionPadic.padicField v
  let A := (P.localComponent v).padicObject (h v).1 (h v).2
  let A' := (P'.localComponent v).padicObject (h' v).1 (h' v).2
  have hc : Correspondence.automorphicClassOf K A = Correspondence.automorphicClassOf K A' := heq
  obtain ⟨e⟩ := (Correspondence.automorphicClassOf_eq_iff K A A').mp hc
  exact Unramified.sphericalSpectrumUniqueness (CompletionPadic.residuePrime v) K r A' _ _
    ((Unramified.hasSphericalSpectrum_iff_of_equiv K e _).mp
      (hasSphericalSpectrum_padicObject P h v hv))
    (hasSphericalSpectrum_padicObject P' h' v hv')

end Realizations

set_option maxHeartbeats 1800000 in
private theorem isoClass_eq_of_splitCentre
    (hcont : CuspidalNondualPartialEulerContinuationStatement.{u,uQ})
    {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
    {T T' : CuspidalOperatorRealization F r}
    (hT : IsTrivialOnSplitCentre T) (hT' : IsTrivialOnSplitCentre T')
    (P : CuspidalSpectralPresentation.{u,uQ} T) (P' : CuspidalSpectralPresentation.{u,uQ} T')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (S : Finset (FinitePlace F)) (hloc : ∀ v ∉ S, localClass P h v = localClass P' h' v) :
    T.isoClass = T'.isoClass := by
  classical
  by_contra hn
  let D := T'.conjugate
  have hD : IsTrivialOnSplitCentre D := Langlands.Global.NormPowerTwist.isTrivialOnSplitCentre_conjugate hT'
  have hunit' := cuspidalSplitCentreUnitaryCentralCharacter F r T' hT'
  have hunitD := cuspidalSplitCentreUnitaryCentralCharacter F r D hD
  have hdual := RankinSelbergGlobal.SelfPair.conjugate_isContragredientOf T' hunit'
  obtain ⟨Pd, hd⟩ := cuspidalContragredientPresentationExistence.{u,uQ,uQ} F r T' D
    hunit' hdual P'
  have hnondual : ¬ T.realization.IsContragredientOf D.realization := by
    intro hcontr
    exact hn ((T.isoClass_eq_iff T').mpr (hcontr.nonempty_equivalence (dual_conjugate hunitD)))
  let S₁ := (S ∪ P.exceptional) ∪ (P'.exceptional ∪ Pd.exceptional)
  have hPS : P.exceptional ⊆ S₁ := fun _ hv =>
    Finset.mem_union_left _ (Finset.mem_union_right _ hv)
  have hP' : P'.exceptional ⊆ S₁ := fun _ hv =>
    Finset.mem_union_right _ (Finset.mem_union_left _ hv)
  have hPd : Pd.exceptional ⊆ S₁ := fun _ hv =>
    Finset.mem_union_right _ (Finset.mem_union_right _ hv)
  have heuler (v : {v : FinitePlace F // v ∉ S₁}) (s : ℂ) :
      partialEulerFactor P Pd hPS hPd v s = partialEulerFactor P' Pd hP' hPd v s := by
    have he := eigenvalues_eq_of_localClass_eq P P' h h' v.1
      (fun hv => v.2 (hPS hv)) (fun hv => v.2 (hP' hv))
      (hloc v.1 (fun hv => v.2 (Finset.mem_union_left _ (Finset.mem_union_left _ hv))))
    unfold partialEulerFactor
    rw [he]
  obtain ⟨L, hL, σ, hprod⟩ := hcont F r T D hT hD P Pd h hd hnondual S₁ hPS hPd
  apply not_exists_entire_selfPair hunit' hdual P' Pd hP' hPd
  exact ⟨L, hL, σ, fun s hs => by
    rw [← funext fun v => heuler v s]
    exact hprod s hs⟩

set_option maxHeartbeats 1800000 in
/-- Strong multiplicity one follows from entire continuation of the nondual
equal-rank partial Euler product. -/
theorem cuspidalStrongMultiplicityOne_of_nondualPartialEulerContinuation
    (hcont : CuspidalNondualPartialEulerContinuationStatement.{u,uQ}) :
    CuspidalStrongMultiplicityOneStatement.{u,uQ} := by
  intro F _ _ _ r T T' P P' h h' S hloc
  obtain ⟨ω, hω, _⟩ := T.realization.existsUnique_hasCentralCharacter T.irreducible
  have hω' := CuspidalCommonSplitCentreTwist.hasCentralCharacter_of_localClass_eq
    P P' h h' S hloc ω hω
  obtain ⟨χ, hχ⟩ := CuspidalCommonSplitCentreTwist.exists_common_splitCentre_twist (r := r) ω
  apply CuspidalCommonSplitCentreTwist.isoClass_eq_of_twist_eq χ
  exact isoClass_eq_of_splitCentre hcont (hχ T hω) (hχ T' hω')
    (P.heckeDeterminantTwist χ) (P'.heckeDeterminantTwist χ)
    (P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ h)
    (P'.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ h') S
    (fun v hv => CuspidalCommonSplitCentreTwist.twist_localClass_eq P P' h h' χ v (hloc v hv))

/-- Strong multiplicity one follows by comparing the mixed and self-pair Euler products. -/
theorem cuspidalStrongMultiplicityOne_of_pairPole :
    CuspidalStrongMultiplicityOneFromPairPole.{u,uQ} := by
  intro hpole
  exact cuspidalStrongMultiplicityOne_of_nondualPartialEulerContinuation
    (cuspidalNondualPartialEulerContinuation_of_pairPole hpole)

end Langlands.Global
