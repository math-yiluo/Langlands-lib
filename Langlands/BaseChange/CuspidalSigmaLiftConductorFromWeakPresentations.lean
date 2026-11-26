import Langlands.BaseChange.CommonTwistPairComparison
import Langlands.BaseChange.CuspidalSigmaLiftConductorFromCompletedEquations
import Langlands.BaseChange.DistinguishedConductorLiftIdentification
import Langlands.BaseChange.DistinguishedEulerRootSeparation

/-! # The conductor formula from weak cyclic base change presentations -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v uV uW

namespace Langlands.BaseChange

open Automorphic Automorphic.ConstantFunctions Global Global.AdelicFunctoriality
open Global.CompletionPadic Global.CuspidalPairFunctionalEquation Global.HeckeFunctionalEquation
open Global.FunctionalEquationComparison GeneralLinear
open HarmonicAnalysis LocalClassField Unramified
open scoped BigOperators FiniteExtension NumberField

local instance weakPresentationRationalGroup (K : Type) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance weakPresentationContinuousGroup (K : Type) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance weakPresentationSmoothGroup (K : Type) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance weakPresentationFormsGroup (K : Type) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _
local instance weakPresentationLocalGroup {K : Type} [Field K] [NumberField K]
    {n : ℕ} {p : FinitePlace K} (D : LocalRealization K n p) :
    AddCommGroup D.Space := Submodule.addCommGroup _

section FactorData

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
  [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)]
  {r : ℕ} {T Td : CuspidalOperatorRealization K r} {U Ud : CuspidalOperatorRealization L r}
  (D : CuspidalSpectralPresentation.{0, 0} T) (Dd : CuspidalSpectralPresentation.{0, 0} Td)
  (Q : CuspidalSpectralPresentation.{0, 0} U) (Qd : CuspidalSpectralPresentation.{0, 0} Ud)
  (hD : HasIrreducibleAdmissibleComponents D) (hDd : HasIrreducibleAdmissibleComponents Dd)
  (hQ : HasIrreducibleAdmissibleComponents Q) (hQd : HasIrreducibleAdmissibleComponents Qd)
  (ν : HeckeCharacter K) (v₀ : FinitePlace K) (w₀ : FinitePlace L)

set_option maxHeartbeats 3100000 in
private theorem hasGlobalStandardFactorComparisons_of_commonTwist
    (hTd : Td.realization.IsContragredientOf T.realization)
    (hUd : Ud.realization.IsContragredientOf U.realization)
    (haux : ∀ p : FinitePlace K, p ≠ v₀ → HasCommonTwistAuxiliaryData D Dd Q Qd hD hDd hQ hQd ν p)
    (hsep :
      let B := rankOneSpectralPresentation.{0, 0} L
      let hB := rankOneSpectralPresentation_hasIrreducibleAdmissibleComponents.{0, 0} L
      ∀ (Ud' : CuspidalOperatorRealization L r),
        Ud'.realization.IsContragredientOf (U.heckeDeterminantTwist (ν.normComp (L := L))).realization →
      ∀ (Qd' : CuspidalSpectralPresentation.{0, 0} Ud') (hQd' : HasIrreducibleAdmissibleComponents Qd')
        (cE : FinitePairFactorChoice (standardGlobalAdditiveCharacter L)
          (Q.heckeDeterminantTwist (ν.normComp (L := L))) B Qd' B
          (Q.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents (ν.normComp (L := L)) hQ) hB hQd' hB)
        (x : ℂ), x ≠ 0 → (cE.lPolynomial w₀).eval x = 0 →
        (cE.dualLPolynomial w₀).eval ((residueCardinality w₀ : ℂ)⁻¹ / x) ≠ 0) :
    HasGlobalStandardFactorComparisons v₀ w₀ (D.heckeDeterminantTwist ν)
      (Q.heckeDeterminantTwist (ν.normComp (L := L)))
      (D.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents ν hD)
      (Q.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents (ν.normComp (L := L)) hQ) := by
  classical
  intro Td' Ud' ht' hu' Dd' Qd' hDd' hQd' χ _ hres C B hC hB cF cE
  let : Fintype ((L ≃ₐ[K] L) →* ℂˣ) := Fintype.ofFinite _
  refine ⟨hsep Ud' hu' Qd' hQd' cE, fun p hp => ?_⟩
  have main := commonTwistPairComparison D Dd Dd' Q Qd Qd' C B hD hDd hDd' hQ hQd hQd' hC hB
    ν _ χ cF cE p hTd hUd ht' hu'
    (rankOneSpectralPresentation_localTrivialEquiv.{0, 0} K p)
    (fun w => rankOneSpectralPresentation_localTrivialEquiv.{0, 0} L w.1) (hres p) (haux p hp)
  simpa only [RelativeWeilEngine.placesAbove, finiteEpsilonBase, Finset.prod_map,
    Function.Embedding.coeFn_mk] using main

end FactorData

/-- Above rank one, the weak base-change presentations have the actual
distinguished local twist and tensor lift at compatible completions. -/
def CuspidalSigmaLiftWeakPresentationDataStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l : ℕ), IsCyclicAlgebra σ l →
    ∀ (k : ℕ), 0 < k →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear (k + 1) F) V)
      (hπ : IsAdmissible π), IsSupercuspidal π → π.IsIrreducible →
    ∀ (s k₁ : ℕ) (h : s * (k₁ + 1) = k + 1)
      (W₁ : Type uW) [AddCommGroup W₁] [Module ℂ W₁]
      (P₁ : Representation ℂ (GeneralLinear (k₁ + 1) E) W₁),
      IsSupercuspidal P₁ → P₁.IsIrreducible →
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (P : Representation ℂ (GeneralLinear (k + 1) E) W) (hP : IsAdmissible P),
      Nonempty (P.Equiv ((sigmaOrbitProduct σ s (Nat.succ_pos k₁) P₁).comp
        (GeneralLinear.reindex (R := E) (finCongr h)).symm.toMonoidHom)) →
    ∀ (A : SigmaIntertwiner σ (k + 1) P) (c : ℂ),
      (haveI := LocalFieldTopology.generalLinear_t2Space F (k + 1)
       haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F (k + 1)
       haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F (k + 1)
       haveI := LocalFieldTopology.generalLinear_t2Space E (k + 1)
       haveI := LocalFieldTopology.generalLinear_locallyCompactSpace E (k + 1)
       haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E (k + 1)
       IsSigmaLift σ l π hπ P hP A c) →
    ∃ (K L : Type) (_ : Field K) (_ : NumberField K) (_ : Field L) (_ : NumberField L)
      (_ : Algebra K L) (_ : IsGalois K L) (_ : IsCyclic (L ≃ₐ[K] L))
      (_ : CompactSpace (AdeleQuotient K)) (_ : CompactSpace (AdeleQuotient L)),
    ∃ (σ₀ : L ≃ₐ[K] L) (p : FinitePlace K) (w : FinitePlacesAbove L p)
      (hw : ∀ w' : FinitePlacesAbove L p, w' = w)
      (a : F ≃+* p.adicCompletion K) (b : E ≃+* w.1.adicCompletion L),
      Continuous a ∧ Continuous a.symm ∧ Continuous b ∧ Continuous b.symm ∧
      (∀ x : F, b (algebraMap F E x) = algebraMap (p.adicCompletion K) (w.1.adicCompletion L) (a x)) ∧
      (∀ x : E, b (σ x) = uniquePlaceCompletionAutEquiv w hw σ₀ (b x)) ∧
    ∃ (T : CuspidalOperatorRealization K k) (U : CuspidalOperatorRealization L k)
      (D : CuspidalSpectralPresentation.{0, 0} T) (Q : CuspidalSpectralPresentation.{0, 0} U),
      HasIrreducibleAdmissibleComponents D ∧ HasIrreducibleAdmissibleComponents Q ∧
    ∃ (R : Representation ℂ (GeneralLinear (k + 1) (p.adicCompletion K)) V)
      (μ : Quasicharacter (p.adicCompletion K)),
      (padicField p).canonicalTopologicalData.IsUnramifiedCharacter μ.toMonoidHom ∧
      Nonempty (π.Equiv (R.comp (Matrix.GeneralLinearGroup.map a.toRingHom))) ∧
      Nonempty ((twist (μ.toMonoidHom.comp determinant) R).Equiv (D.localComponent p).representation) ∧
      IsLiftAtDistinguishedTensor w hw σ₀ l (D.localComponent p) (Q.localComponent w.1) ∧
      (D.localComponent p).IsSupercuspidal ∧ Q.spectralSystem.IsArithmeticWeakBaseChangeOf D.spectralSystem

set_option maxHeartbeats 7600000 in
/-- Choose the common twist on the original weak presentations. By local
triviality their distinguished actions persist, and the auxiliary factors
of the twisted presentations agree everywhere else. -/
theorem cuspidalSigmaLiftGlobalFactorData_of_weakPresentations
    (hUnique : SigmaLiftUniquenessStatement.{u, v, uV, uW, 0})
    (hdata : CuspidalSigmaLiftWeakPresentationDataStatement.{u, v, uV, uW}) :
    CuspidalSigmaLiftGlobalFactorDataStatement.{u, v, uV, uW} := by
  intro F _ _ _ _ _ E _ _ _ _ _ _ σ l hcyc k hk V _ _ π hπ hπs hπi
    s k₁ hrank W₁ _ _ P₁ hP₁s hP₁i W _ _ P hP horbit A c hlift
  let : FiniteDimensional F E := hcyc.1
  obtain ⟨K, L, fK, nK, fL, nL, aKL, gKL, cKL, compactK, compactL, σ₀, p, w, hw, a, b, ha, ha', hb, hb',
    hab, hσb, T, U, D, Q, hD, hQ, R, μ, hμ, eπ, eR, hLift, hDs, hweak⟩ :=
    hdata F E σ l hcyc k hk V π hπ hπs hπi s k₁ hrank W₁ P₁ hP₁s hP₁i
      W P hP horbit A c hlift
  let S := P.comp (Matrix.GeneralLinearGroup.map b.symm.toRingHom)
  have eP : Nonempty (P.Equiv (S.comp (Matrix.GeneralLinearGroup.map b.toRingHom))) := by
    let bG := fieldEquiv (k + 1) b hb hb'
    have heq : S.comp (Matrix.GeneralLinearGroup.map b.toRingHom) = P :=
      MonoidHom.ext fun g => congrArg P (bG.symm_apply_apply g)
    exact ⟨equivOfRepresentationEq heq.symm⟩
  have hLiftCompletion := distinguishedTensorLiftTransport K L k p w hw σ₀ l
    (D.localComponent p) (Q.localComponent w.1) (hD p).2 (hQ w.1).2 hLift
  let η := μ.toMonoidHom.comp (normUnits (p.adicCompletion K) (w.1.adicCompletion L))
  have ⟨hη, eS⟩ := distinguishedConductorLiftIdentification hUnique K L p w F E σ l hcyc
    a b ha ha' hb hb' hab (uniquePlaceCompletionAutEquiv w hw σ₀) hσb
    k V π hπ hπi s k₁ hrank W₁ P₁ hP₁i hP₁s W P hP horbit A c hlift R S eπ eP
    (D.localComponent p) (Q.localComponent w.1) (hD p).2 (hQ w.1).2 (hQ w.1).1 hLiftCompletion
    μ hμ eR
  have hb₀ : @Continuous E (padicField w.1).Carrier ‹TopologicalSpace E›
      (padicField w.1).canonicalTopologicalData.topology b := by
    rw [← completion_topology_eq w.1]
    exact hb
  have hb₁ : @Continuous (padicField w.1).Carrier E (padicField w.1).canonicalTopologicalData.topology
      ‹TopologicalSpace E› b.symm := by
    rw [← completion_topology_eq w.1]
    exact hb'
  obtain ⟨Td, Dd, hTd, hDd⟩ := exists_cuspidalContragredient_presentation.{0, 0} K T
  obtain ⟨Ud, Qd, hUd, hQd⟩ := exists_cuspidalContragredient_presentation.{0, 0} L U
  obtain ⟨ν, _, hν, hν', haux⟩ := weakBaseChangeAuxiliaryTwist D Dd Q Qd hD hDd hQ hQd p hweak
  let ξ := ν.normComp (L := L)
  let D' := D.heckeDeterminantTwist ν
  let Q' := Q.heckeDeterminantTwist ξ
  have hD' := D.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents ν hD
  have hQ' := Q.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents ξ hQ
  have eR' : Nonempty ((twist (μ.toMonoidHom.comp determinant) R).Equiv
      (D'.localComponent p).representation) :=
    eR.map fun e => e.trans (heckeTwistAtCompletionEquiv_of_trivial D p ν hν)
  have eS' : Nonempty ((twist (η.comp determinant) S).Equiv (Q'.localComponent w.1).representation) :=
    eS.map fun e => e.trans (heckeTwistAtCompletionEquiv_of_trivial Q w.1 ξ (hν' w))
  have hloc : HasGlobalStandardFactorComparisons p w.1 D' Q' hD' hQ' := by
    refine hasGlobalStandardFactorComparisons_of_commonTwist D Dd Q Qd hD hDd hQ hQd ν p w.1 hTd hUd haux ?_
    intro B hB Ud' hUd' Qd' hQd' cE
    exact distinguishedEulerRootSeparationOfUnramifiedOrbit Q' Qd' hQ' hQd' cE w.1 b P σ hrank P₁ S η
      hb₀ hb₁ hk hUd' hP₁i hP₁s horbit hη eP eS'
  exact ⟨K, L, fK, nK, fL, nL, aKL, gKL, cKL, compactK, compactL, p, w, a, b, hw, ha, ha', hb, hb',
    RingHom.ext fun x => (hab x).symm, _, _, D', Q', hD', hQ', R, S, μ.toMonoidHom, η,
    hμ, hη, eπ, eP, eR', eS', heckeDeterminantTwistSupercuspidal K T D ν p hDs, hloc⟩

/-- Completed cuspidal-pair functional equations, local lift uniqueness
and weak cyclic presentation data imply the conductor formula. -/
def CuspidalSigmaLiftConductorFromWeakPresentationsStatement : Prop :=
  CuspidalPairGlobalFunctionalEquationStatement.{0, 0} →
    SigmaLiftUniquenessStatement.{u, v, uV, uW, 0} →
    CuspidalSigmaLiftWeakPresentationDataStatement.{u, v, uV, uW} →
      CuspidalSigmaLiftConductorStatement.{u, v, uV, uW}

theorem cuspidalSigmaLiftConductorFromWeakPresentations :
    CuspidalSigmaLiftConductorFromWeakPresentationsStatement.{u, v, uV, uW} :=
  fun hFE hUnique hdata => cuspidalSigmaLiftConductorFromCompletedEquations hFE
    (cuspidalSigmaLiftGlobalFactorData_of_weakPresentations hUnique hdata)

end Langlands.BaseChange
