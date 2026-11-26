import Langlands.Automorphic.AssociatedAdditiveInputs
import Langlands.Automorphic.AssociatedPresentationComparison
import Langlands.Automorphic.ContragredientSymmetry
import Langlands.Automorphic.CuspidalContragredientArithmetic
import Langlands.Automorphic.Unramified.CyclicWeakInductionSelfPairGamma
import Langlands.Automorphic.Unramified.NormTwistedPairGammaOrder
import Langlands.Automorphic.Unramified.WeakInductionContragredient
import Langlands.Automorphic.Unramified.WeakInductionOrbitPairEuler
import Langlands.Correspondence.AutomorphicGammaGerm
import Langlands.Global.Factors.CuspidalArchimedeanParameterExistenceProof

/-! # Self-pair gamma orders of cyclic weak inductions from equal-rank equations -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe uF uE uV uW

namespace Langlands.Automorphic.Unramified

open Filter Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Global.CompletionPadic Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.Global.FunctionalEquationComparison Langlands.Global.HeckeFunctionalEquation
open CuspidalOperatorRealization Correspondence RankinSelberg LocalFactor
open scoped NumberField Classical

section PairSetup

variable {K : Type uF} [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]

local instance gammaMatchingRationalGroup (n : ℕ) : AddCommGroup (RationalInvariantFunctions K n) :=
  Submodule.addCommGroup _
local instance gammaMatchingContinuousGroup (n : ℕ) : AddCommGroup (ContinuousRationalFunctions K n) :=
  Submodule.addCommGroup _
local instance gammaMatchingSmoothGroup (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions K n) :=
  Submodule.addCommGroup _
local instance gammaMatchingFormsGroup (n : ℕ) : AddCommGroup (AutomorphicForms K n) :=
  Submodule.addCommGroup _
local instance gammaMatchingLocalAddCommGroup {n : ℕ} {v : FinitePlace K}
    (A : LocalRealization K n v) : AddCommGroup A.Space := Submodule.addCommGroup _

set_option maxHeartbeats 1000000 in
private theorem irreduciblePresentation (r : ℕ) (T : CuspidalOperatorRealization K r) :
    ∃ P : CuspidalSpectralPresentation.{uF,uV} T, HasIrreducibleAdmissibleComponents P := by
  obtain ⟨A, hA, hI⟩ := cuspidalIrreducibleAdmissibleFiniteSliceExistence K r T
  obtain ⟨P, hP⟩ := T.exists_presentation_of_finiteSlice A hA hI
  exact P.exists_small hP

omit [CompactSpace (AdeleQuotient K)] in
private theorem standardCharacter_ne_one : ∃ x : Adeles K, standardGlobalAdditiveCharacter K x ≠ 1 :=
  CuspidalWhittaker.exists_adelicCharacter_ne_one K

set_option maxHeartbeats 1000000 in
private abbrev standardPairSetup {r t : ℕ}
    {T Td : CuspidalOperatorRealization K r} {U Ud : CuspidalOperatorRealization K t}
    (hTd : Td.realization.IsContragredientOf T.realization)
    (hUd : Ud.realization.IsContragredientOf U.realization)
    (P : CuspidalSpectralPresentation.{uF,uV} T) (Q : CuspidalSpectralPresentation.{uF,uV} U)
    (Pd : CuspidalSpectralPresentation.{uF,uV} Td) (Qd : CuspidalSpectralPresentation.{uF,uV} Ud)
    (hP : HasIrreducibleAdmissibleComponents P) (hQ : HasIrreducibleAdmissibleComponents Q)
    (hPd : HasIrreducibleAdmissibleComponents Pd) (hQd : HasIrreducibleAdmissibleComponents Qd) :
    AutomorphicTwistSetup.{uF,uV} (standardGlobalAdditiveCharacter K) r t := by
  let ψ := standardGlobalAdditiveCharacter K
  have hdiag : ∀ x : K, ψ (diagonal K x) = 1 := standardGlobalAdditiveCharacter_diagonal K
  have hR := exists_isRealAdditiveComponent ψ hdiag
  have hC := exists_isComplexAdditiveComponent ψ hdiag
  have hT₀ := cuspidalArchimedeanParameterExistence K r T
  have hTd₀ := cuspidalArchimedeanParameterExistence K r Td
  have hU₀ := cuspidalArchimedeanParameterExistence K t U
  have hUd₀ := cuspidalArchimedeanParameterExistence K t Ud
  exact {
    T := T, T' := U, Td := Td, Td' := Ud, hTd := hTd, hTd' := hUd
    P := P, P' := Q, Pd := Pd, Pd' := Qd, h := hP, h' := hQ, hd := hPd, hd' := hQd
    additive := standardFiniteAdditiveComponent K
    additive_spec := isCanonicalFiniteAdditiveComponent_standardFiniteAdditiveComponent K
    measure := fun v => localSelfDualHaar (padicField v) (standardFiniteAdditiveComponent K v)
    measure_spec := fun v => isSelfDual_localSelfDualHaar (padicField v) (standardFiniteAdditiveComponent K v)
    aR := fun v => (hR v).choose, aR_spec := fun v => (hR v).choose_spec
    aC := fun v => (hC v).choose, aC_spec := fun v => (hC v).choose_spec
    dR := fun v => (hT₀.1 v).choose, dR_spec := fun v => (hT₀.1 v).choose_spec
    dR' := fun v => (hU₀.1 v).choose, dR'_spec := fun v => (hU₀.1 v).choose_spec
    dRd := fun v => (hTd₀.1 v).choose, dRd_spec := fun v => (hTd₀.1 v).choose_spec
    dRd' := fun v => (hUd₀.1 v).choose, dRd'_spec := fun v => (hUd₀.1 v).choose_spec
    dC := fun v => (hT₀.2 v).choose, dC_spec := fun v => (hT₀.2 v).choose_spec
    dC' := fun v => (hU₀.2 v).choose, dC'_spec := fun v => (hU₀.2 v).choose_spec
    dCd := fun v => (hTd₀.2 v).choose, dCd_spec := fun v => (hTd₀.2 v).choose_spec
    dCd' := fun v => (hUd₀.2 v).choose, dCd'_spec := fun v => (hUd₀.2 v).choose_spec
    w₀ := Classical.arbitrary _ }

set_option maxHeartbeats 1500000 in
private theorem untwisted_dualPair_gamma
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles K)} {r : ℕ}
    (D : AutomorphicTwistSetup.{uF,uV} ψ r r) (v : FinitePlace K)
    (A : CuspidalSpectralPresentation.{uF,uV} D.T)
    (B : CuspidalSpectralPresentation.{uF,uV} D.Td')
    (hA : (A.localComponent v).IsIrreducible)
    (hBi : (B.localComponent v).IsIrreducible) (hBa : (B.localComponent v).IsAdmissible) :
    let ν : PadicAbelian.SelfDualHaar (padicField v).canonicalTopologicalData (D.additive v) :=
      ⟨D.measure v, D.measure_spec v⟩
    ∃ G : RatFunc ℂ, HasLocalDualPairGamma (A.localComponent v) (B.localComponent v) (D.additive v) ν G ∧
      ∀ z : ℂ, meromorphicOrderAt (rationalSpectralValue (residueCardinality v) G) z =
        meromorphicOrderAt (D.localFactors 1 (.inr v)).gamma z := by
  dsimp only
  let L := padicField v
  let ν : PadicAbelian.SelfDualHaar L.canonicalTopologicalData (D.additive v) :=
    ⟨D.measure v, D.measure_spec v⟩
  have hd := twistedPairData_spec (D.additive v) (D.measure_spec v)
    (localClass D.P D.h v) (localClass D.P' D.h' v)
    (quasicharacterBase v ((1 : HeckeCharacter K).finiteComponent v))
  have hPd : (D.finiteData 1 v).2.1 ≠ 0 := by
    obtain ⟨_, _, _, _, _, _, _, hPd, _⟩ := hd
    exact hPd.ne_zero
  obtain ⟨πη, htw, hG⟩ := IsTwistedPairData.exists_gamma hd
  have hOne : quasicharacterBase v ((1 : HeckeCharacter K).finiteComponent v) = 1 := by
    apply DFunLike.ext
    intro a
    rfl
  rw [hOne] at htw
  obtain rfl := htw.unique (Correspondence.isCharacterTwist_one _)
  let A₀ := (D.P.localComponent v).padicObject (D.h v).1 (D.h v).2
  let B₀ := (D.P'.localComponent v).padicObject (D.h' v).1 (D.h' v).2
  have hA₀ := CuspidalPairPartialGamma.localGenericity K r D.T D.P v (D.h v).1 (D.h v).2 (D.additive v)
  have hB₀ := CuspidalPairPartialGamma.localGenericity K r D.T' D.P' v (D.h' v).1 (D.h' v).2 (D.additive v)
  have hΓ := hG.isPadicSymmetricGammaFactor_of_generic (ν := ν)
    genericLanglandsPairEpsilonFactorComparison A₀ B₀ hA₀ hB₀
  obtain ⟨a⟩ := D.P.nonempty_localComponent_equiv A v (D.h v).1 hA
  obtain ⟨b⟩ := cuspidalContragredientLocalCompatibility K r D.Td' D.T'
    (isContragredientOf_symm D.hTd') B D.P' v hBi hBa (D.h' v).1 (D.h' v).2
  refine ⟨_, (IsPadicSymmetricGammaFactor.congr_equiv a b).mp hΓ, fun z => ?_⟩
  exact meromorphicOrderAt_congr (rationalSpectralValue_eventuallyEq_polynomialGammaExpression
    (residueCardinality v) (FinitePairFactorChoice.one_lt_residueCardinality v)
    (residueReflection L) (D.finiteData 1 v).2.2.1 (coe_residueReflection L)
    (D.finiteData 1 v).2.2.2 (D.finiteData 1 v).1 (D.finiteData 1 v).2.1 hPd z)

set_option maxHeartbeats 500000 in
private theorem standard_setup_dualPair_gamma {r : ℕ}
    {T Td U Ud : CuspidalOperatorRealization K r}
    (hTd : Td.realization.IsContragredientOf T.realization)
    (hUd : Ud.realization.IsContragredientOf U.realization)
    (P : CuspidalSpectralPresentation.{uF,uV} T) (Q : CuspidalSpectralPresentation.{uF,uV} U)
    (Pd : CuspidalSpectralPresentation.{uF,uV} Td) (Qd : CuspidalSpectralPresentation.{uF,uV} Ud)
    (hP : HasIrreducibleAdmissibleComponents P) (hQ : HasIrreducibleAdmissibleComponents Q)
    (hPd : HasIrreducibleAdmissibleComponents Pd) (hQd : HasIrreducibleAdmissibleComponents Qd)
    (v : FinitePlace K) (A : CuspidalSpectralPresentation.{uF,uV} T)
    (B : CuspidalSpectralPresentation.{uF,uV} Ud)
    (hA : (A.localComponent v).IsIrreducible)
    (hBi : (B.localComponent v).IsIrreducible) (hBa : (B.localComponent v).IsAdmissible) :
    let ψ := standardFiniteAdditiveComponent K v
    let ν : PadicAbelian.SelfDualHaar (padicField v).canonicalTopologicalData ψ :=
      ⟨localSelfDualHaar (padicField v) ψ, isSelfDual_localSelfDualHaar (padicField v) ψ⟩
    let D := standardPairSetup hTd hUd P Q Pd Qd hP hQ hPd hQd
    ∃ G : RatFunc ℂ, HasLocalDualPairGamma (A.localComponent v) (B.localComponent v) ψ ν G ∧
      ∀ z : ℂ, meromorphicOrderAt (rationalSpectralValue (residueCardinality v) G) z =
        meromorphicOrderAt (D.localFactors 1 (.inr v)).gamma z := by
  let D : AutomorphicTwistSetup.{uF,uV} (standardGlobalAdditiveCharacter K) r r :=
    standardPairSetup hTd hUd P Q Pd Qd hP hQ hPd hQd
  let A' : CuspidalSpectralPresentation.{uF,uV} D.T := A
  let B' : CuspidalSpectralPresentation.{uF,uV} D.Td' := B
  have hA' : (A'.localComponent v).IsIrreducible := by
    dsimp only [A', D, standardPairSetup]
    exact hA
  have hBi' : (B'.localComponent v).IsIrreducible := by
    dsimp only [B', D, standardPairSetup]
    exact hBi
  have hBa' : (B'.localComponent v).IsAdmissible := by
    dsimp only [B', D, standardPairSetup]
    exact hBa
  have hg := @untwisted_dualPair_gamma.{uF,uV} K _ _ _ (standardGlobalAdditiveCharacter K)
    r D v A' B' hA' hBi' hBa'
  exact hg

end PairSetup

/-- The functional-equation inputs for equal-rank twist families and the weak
base-change identity for the full upper orbit give the self-pair gamma comparison
at a unique finite place. -/
def CyclicWeakInductionGammaOrderFromTwistEquationsStatement : Prop :=
  EqualRankTwistEngineInputsStatement.{uF,uV} →
  EqualRankTwistEngineInputsStatement.{uE,uW} →
  WeakInductionOrbitBaseChangeStatement.{uF,uE,uV,uW} →
  CyclicWeakInductionSelfPairGammaOrderAtUniquePlaceStatement.{uF,uE,uV,uW}

set_option maxHeartbeats 800000 in
/-- The equal-rank equations at the supplied base and extension fields give the local
self-pair order comparison by the cofinite orbit identity and the two-twist comparison. -/
theorem cyclicWeakInductionGammaOrderAtFromTwistEquations
    (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    [CompactSpace (AdeleQuotient E)]
    (hFE : EqualRankTwistEngineInputsAt.{uF,uV} F)
    (hFEE : EqualRankTwistEngineInputsAt.{uE,uW} E)
    (hOrbit : WeakInductionOrbitBaseChangeStatement.{uF,uE,uV,uW}) :
    CyclicWeakInductionSelfPairGammaOrderAtUniquePlace.{uF,uE,uV,uW} F E := by
  intro _ σ hgen v w hw r m S T Q₀ P₀ U R₀
    _ _ hQi hQa hPsc hRsc hConj hWeak
  obtain ⟨Sd, hSd⟩ := cuspidalContragredientExistence F r S
  obtain ⟨Td, hTd⟩ := cuspidalContragredientExistence E m T
  let I := Fin (Module.finrank F E)
  choose Ud hUd using fun i : I => cuspidalContragredientExistence E m (U i)
  have hConjd (i : I) : Td.isoClass.IsGaloisConjugate (σ ^ (i : ℕ)) (Ud i).isoClass :=
    IsoClass.isGaloisConjugate_contragredient _ (hConj i) hTd (hUd i)
  obtain ⟨Q, hQ⟩ := irreduciblePresentation.{uF,uV} r S
  obtain ⟨Qd, hQd⟩ := irreduciblePresentation.{uF,uV} r Sd
  obtain ⟨P, hP⟩ := irreduciblePresentation.{uE,uW} m T
  obtain ⟨Pd, hPd⟩ := irreduciblePresentation.{uE,uW} m Td
  choose R hR using fun i : I => irreduciblePresentation.{uE,uW} m (U i)
  choose Rd hRd using fun i : I => irreduciblePresentation.{uE,uW} m (Ud i)
  let D := standardPairSetup hSd (isContragredientOf_symm hSd) Q Qd Qd Q hQ hQd hQd hQ
  let A (i : I) := standardPairSetup hTd (isContragredientOf_symm (hUd i))
    P (Rd i) Pd (R i) hP (hRd i) hPd (hR i)
  have hWeakd : Sd.isoClass.IsWeakInductionOf.{uF,uE,uV,uW} Td.isoClass :=
    (IsoClass.isWeakInductionOf_isoClass_iff Sd Td).mpr
      ⟨Qd, Pd, weakInductionContragredient F E S Sd T Td Qd Pd hSd hTd hWeak⟩
  have hForward := weakInductionOrbitPairEulerValues hOrbit F E σ hgen S Sd T Td Ud
    Q Qd P Rd hConjd hWeak hWeakd
  have hReflected := weakInductionOrbitPairEulerValues hOrbit F E σ hgen Sd S Td T U
    Qd Q Pd R hConj hWeakd hWeak
  have hMatch : CofiniteSphericalPairMatching D A := by
    filter_upwards [hForward, hReflected, eventually_ramificationIdx_eq_one F E] with p hf hd hp
    obtain ⟨hfQ, hfQd, hfP, hfRd, hf⟩ := hf
    obtain ⟨hdQd, hdQ, hdPd, hdR, hd⟩ := hd
    have hD : D.SphericalAt p := ⟨hfQ, hfQd, hdQd, hdQ⟩
    have hA (i : I) (q : FinitePlacesAbove E p) : (A i).SphericalAt q.1 :=
      ⟨hfP q, hfRd i q, hdPd q, hdR i q⟩
    refine ⟨hD, hA, fun q => hp q.1 q.2, fun z => ⟨?_, ?_⟩⟩
    · rw [(spherical_factors_one D p hD z).1, (numberFieldProductFactors_finite _ p z).1]
      simp_rw [fun (q : FinitePlacesAbove E p) (i : I) => (spherical_factors_one (A i) q.1 (hA i q) z).1]
      exact hf z
    · rw [(spherical_factors_one D p hD z).2, (numberFieldProductFactors_finite _ p z).2.1]
      simp_rw [fun (q : FinitePlacesAbove E p) (i : I) => (spherical_factors_one (A i) q.1 (hA i q) z).2]
      exact hd z
  have hOrder (z : ℂ) : meromorphicOrderAt (D.localFactors 1 (.inr v)).gamma z =
      ∑ q : FinitePlacesAbove E v, ∑ i : I,
        meromorphicOrderAt ((A i).localFactors 1 (.inr q.1)).gamma z :=
    normTwistedPairGammaOrder.{uF,uE,uV,uW,0} F E I
      (ψ := standardGlobalAdditiveCharacter F) (ψE := standardGlobalAdditiveCharacter E)
      (r := r) (t := r) (m := m) (n := m) D A
      (hFE _ (standardCharacter_ne_one (K := F)) (standardGlobalAdditiveCharacter_diagonal F) r D)
      (fun i => hFEE _ (standardCharacter_ne_one (K := E))
        (standardGlobalAdditiveCharacter_diagonal E) m (A i))
      hMatch v z
  obtain ⟨G, hG, hEval⟩ := standard_setup_dualPair_gamma hSd (isContragredientOf_symm hSd)
    Q Qd Qd Q hQ hQd hQd hQ v Q₀ Q₀ hQi hQi hQa
  have hCertificates (i : I) := standard_setup_dualPair_gamma hTd (isContragredientOf_symm (hUd i))
    P (Rd i) Pd (R i) hP (hRd i) hPd (hR i) w.1 P₀ (R₀ i)
    hPsc.choose (hRsc i).choose (hRsc i).choose_spec.choose
  choose H hH hEval' using hCertificates
  let ψv := standardFiniteAdditiveComponent F v
  let ψw := standardFiniteAdditiveComponent E w.1
  let νv : PadicAbelian.SelfDualHaar (padicField v).canonicalTopologicalData ψv :=
    ⟨localSelfDualHaar (padicField v) ψv, isSelfDual_localSelfDualHaar (padicField v) ψv⟩
  let νw : PadicAbelian.SelfDualHaar (padicField w.1).canonicalTopologicalData ψw :=
    ⟨localSelfDualHaar (padicField w.1) ψw, isSelfDual_localSelfDualHaar (padicField w.1) ψw⟩
  refine ⟨ψv, νv, ψw, νw, G, H, hG, hH, fun s => ?_⟩
  have hUniv : (Finset.univ : Finset (FinitePlacesAbove E v)) = {w} := by
    ext q
    simp [hw q]
  change meromorphicOrderAt (rationalSpectralValue (residueCardinality v) G) (s : ℂ) =
    ∑ i, meromorphicOrderAt (rationalSpectralValue (residueCardinality w.1) (H i)) (s : ℂ)
  rw [hEval, hOrder, hUniv, Finset.sum_singleton]
  exact Finset.sum_congr rfl fun i _ => (hEval' i (s : ℂ)).symm

theorem cyclicWeakInductionGammaOrderFromTwistEquations :
    CyclicWeakInductionGammaOrderFromTwistEquationsStatement.{uF,uE,uV,uW} := by
  intro hFE hFEE hOrbit F E _ _ _ _ _ _ _ _
  exact cyclicWeakInductionGammaOrderAtFromTwistEquations F E (hFE F) (hFEE E) hOrbit

end Langlands.Automorphic.Unramified
