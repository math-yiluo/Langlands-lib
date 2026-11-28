import Langlands.Automorphic.ContragredientSymmetry
import Langlands.BaseChange.CuspidalPairDistinguishedNormEuler
import Langlands.BaseChange.DegreeOneSigmaSelfPairEuler
import Langlands.BaseChange.DistinguishedNormCharacters
import Langlands.BaseChange.DistinguishedPairPolynomialTransport
import Langlands.BaseChange.DistinguishedSigmaLiftMatch
import Langlands.BaseChange.DistinguishedStandardEpsilonExponent
import Langlands.BaseChange.DistinguishedTensorLiftTransport
import Langlands.BaseChange.CyclicGlobalizationWithSplitPlaces
import Langlands.BaseChange.PseudoCoefficientExistenceReduction
import Langlands.BaseChange.RankOneSelfPairLFactorComparison
import Langlands.BaseChange.StandardCompletedTwistEquation
import Langlands.BaseChange.SupercuspidalNormTwistedPairPolynomial
import Langlands.BaseChange.TemperedSelfPairEulerRootRegion
import Langlands.Global.Factors.CuspidalArchimedeanParameterExistenceProof
import Langlands.Representation.Classification.InverseTransposeAnalyticProof
import Langlands.TraceFormula.CuspidalCyclicBaseChangeLiftAnyDegreeStatement
import Langlands.TraceFormula.GeneralLinearDiscreteSeriesGlobalizationStatement

/-! # The local self-pair Euler comparison from cyclic globalization -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v uV uW

namespace Langlands.BaseChange

open Automorphic Automorphic.CuspidalOperatorRealization Correspondence GeneralLinear Global Global.AdelicFunctoriality
open Global.CompletionPadic Global.CuspidalPairFunctionalEquation Global.HeckeFunctionalEquation
open Global.FunctionalEquationComparison HarmonicAnalysis LocalClassField LocalFactor RankinSelberg TraceFormula
open PadicAbelian Unramified
open scoped BigOperators FiniteExtension NNReal NumberField

private local instance selfPairRationalAddCommGroup (K : Type) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
private local instance selfPairContinuousAddCommGroup (K : Type) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
private local instance selfPairSmoothAddCommGroup (K : Type) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
private local instance selfPairFormAddCommGroup (K : Type) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _
private local instance selfPairLocalAddCommGroup {K : Type} [Field K] [NumberField K]
    {n : ℕ} {w : FinitePlace K} (A : LocalRealization K n w) : AddCommGroup A.Space :=
  Submodule.addCommGroup _

section GlobalPair

variable {K : Type} [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]

set_option maxHeartbeats 1100000 in
private abbrev standardSelfPairSetup {r : ℕ} {T Td : CuspidalOperatorRealization K r}
    (hTd : Td.realization.IsContragredientOf T.realization)
    (P : CuspidalSpectralPresentation.{0,0} T) (Pd : CuspidalSpectralPresentation.{0,0} Td)
    (hP : HasIrreducibleAdmissibleComponents P) (hPd : HasIrreducibleAdmissibleComponents Pd) :
    AutomorphicTwistSetup.{0,0} (standardGlobalAdditiveCharacter K) r r := by
  let ψ := standardGlobalAdditiveCharacter K
  have hdiag : ∀ x : K, ψ (diagonal K x) = 1 := standardGlobalAdditiveCharacter_diagonal K
  have hR := exists_isRealAdditiveComponent ψ hdiag
  have hC := exists_isComplexAdditiveComponent ψ hdiag
  have hT := cuspidalArchimedeanParameterExistence K r T
  have hD := cuspidalArchimedeanParameterExistence K r Td
  exact {
    T := T, T' := Td, Td := Td, Td' := T
    hTd := hTd, hTd' := isContragredientOf_symm hTd
    P := P, P' := Pd, Pd := Pd, Pd' := P, h := hP, h' := hPd, hd := hPd, hd' := hP
    additive := standardFiniteAdditiveComponent K
    additive_spec := isCanonicalFiniteAdditiveComponent_standardFiniteAdditiveComponent K
    measure := fun w => localSelfDualHaar (padicField w) (standardFiniteAdditiveComponent K w)
    measure_spec := fun w => isSelfDual_localSelfDualHaar (padicField w) (standardFiniteAdditiveComponent K w)
    aR := fun w => (hR w).choose, aR_spec := fun w => (hR w).choose_spec
    aC := fun w => (hC w).choose, aC_spec := fun w => (hC w).choose_spec
    dR := fun w => (hT.1 w).choose, dR_spec := fun w => (hT.1 w).choose_spec
    dR' := fun w => (hD.1 w).choose, dR'_spec := fun w => (hD.1 w).choose_spec
    dRd := fun w => (hD.1 w).choose, dRd_spec := fun w => (hD.1 w).choose_spec
    dRd' := fun w => (hT.1 w).choose, dRd'_spec := fun w => (hT.1 w).choose_spec
    dC := fun w => (hT.2 w).choose, dC_spec := fun w => (hT.2 w).choose_spec
    dC' := fun w => (hD.2 w).choose, dC'_spec := fun w => (hD.2 w).choose_spec
    dCd := fun w => (hD.2 w).choose, dCd_spec := fun w => (hD.2 w).choose_spec
    dCd' := fun w => (hT.2 w).choose, dCd'_spec := fun w => (hT.2 w).choose_spec
    w₀ := Classical.arbitrary _ }

set_option maxHeartbeats 1500000 in
private theorem contragredient_spectrum {r : ℕ} {T Td : CuspidalOperatorRealization K r}
    (hTd : Td.realization.IsContragredientOf T.realization)
    (P : CuspidalSpectralPresentation.{0,0} T) (Pd : CuspidalSpectralPresentation.{0,0} Td)
    (hP : HasIrreducibleAdmissibleComponents P) (hPd : HasIrreducibleAdmissibleComponents Pd)
    (w : FinitePlace K) (hw : w ∉ P.spectralSystem.exceptional)
    (hwd : w ∉ Pd.spectralSystem.exceptional) :
    Pd.spectralSystem.eigenvalues w hwd = (P.spectralSystem.eigenvalues w hw).map Inv.inv := by
  let F := padicField w
  let A := (Pd.localComponent w).padicObject (hPd w).1 (hPd w).2
  have ha : HasSphericalHeckeSpectrum F A (Pd.spectralSystem.eigenvalues w hwd) :=
    (hasSphericalHeckeSpectrumClass_classOf F A _).mp
      (((Pd.localComponent w).hasSphericalHeckeSpectrumClass_iff (hPd w).1 (hPd w).2 _).mpr
        (Pd.hasSpectrum w hwd))
  have hb := dualSphericalSpectrumAtCompletion K r T Td hTd P Pd hP hPd w hw
  obtain ⟨z, hz, hc⟩ := hb
  rw [← hz]
  exact eq_of_hasSphericalHeckeSpectrum F ha (hasSphericalHeckeSpectrum_of_isSphericalConstituent F hc)

set_option maxHeartbeats 1300000 in
private theorem contragredient_weakBaseChange
    {L : Type} [Field L] [NumberField L] [Algebra K L] [CompactSpace (AdeleQuotient L)]
    {r : ℕ} {T Td : CuspidalOperatorRealization K r} {U Ud : CuspidalOperatorRealization L r}
    (hTd : Td.realization.IsContragredientOf T.realization) (hUd : Ud.realization.IsContragredientOf U.realization)
    (P : CuspidalSpectralPresentation.{0,0} T) (Pd : CuspidalSpectralPresentation.{0,0} Td)
    (Q : CuspidalSpectralPresentation.{0,0} U) (Qd : CuspidalSpectralPresentation.{0,0} Ud)
    (hP : HasIrreducibleAdmissibleComponents P) (hPd : HasIrreducibleAdmissibleComponents Pd)
    (hQ : HasIrreducibleAdmissibleComponents Q) (hQd : HasIrreducibleAdmissibleComponents Qd)
    (h : Q.spectralSystem.IsArithmeticWeakBaseChangeOf P.spectralSystem) :
    Qd.spectralSystem.IsArithmeticWeakBaseChangeOf Pd.spectralSystem := by
  classical
  filter_upwards [h, Pd.spectralSystem.exceptional.eventually_cofinite_notMem,
    SpectralSystem.eventually_avoidsAbove (F := K) Qd.spectralSystem.exceptional] with w hw hd he
  obtain ⟨hp, hq, hram, hspec⟩ := hw
  refine ⟨hd, he, hram, fun z => ?_⟩
  rw [contragredient_spectrum hTd P Pd hP hPd w hp hd,
    contragredient_spectrum hUd Q Qd hQ hQd z.1 (hq z) (he z), hspec z]
  simp [Eigenvalues.power, Sym.map_map]

end GlobalPair

section LocalPair

variable {K : Type} [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)]
  {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

private local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
private local instance (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n

set_option maxHeartbeats 1600000 in
private theorem compareCuspidalPolynomial {r : ℕ} {T U : CuspidalOperatorRealization K r}
    (P : CuspidalSpectralPresentation.{0,0} T) (Q : CuspidalSpectralPresentation.{0,0} U)
    (hP : HasIrreducibleAdmissibleComponents P) (hQ : HasIrreducibleAdmissibleComponents Q)
    (w : FinitePlace K) (a : F.Carrier ≃+* w.adicCompletion K) (ha : Continuous a) (ha' : Continuous a.symm)
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) W)
    (eρ : ρ.Equiv ((P.localComponent w).representation.comp (Matrix.GeneralLinearGroup.map a.toRingHom)))
    (eτ : τ.Equiv ((Q.localComponent w).representation.comp (Matrix.GeneralLinearGroup.map a.toRingHom)))
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : SelfDualHaar F.canonicalTopologicalData ψ)
    (φ : NontrivialAdditiveCharacter (padicField w))
    (ξ : SelfDualHaar (padicField w).canonicalTopologicalData φ) {A B : Polynomial ℂ}
    (hA : IsPadicRankLPolynomial F ψ ν.val ρ τ A)
    (hB : IsAutomorphicPairLPolynomial (padicField w) φ ξ.val (localClass P hP w) (localClass Q hQ w) B) :
    A = B := by
  have h₁ : @Continuous F.Carrier (padicField w).Carrier _ (padicField w).canonicalTopologicalData.topology a := by
    rw [← completion_topology_eq w]
    exact ha
  have h₂ : @Continuous (padicField w).Carrier F.Carrier (padicField w).canonicalTopologicalData.topology _ a.symm := by
    rw [← completion_topology_eq w]
    exact ha'
  exact distinguishedPairPolynomialTransport p (residuePrime w) F (padicField w) a h₁ h₂
    r V W ρ τ ((P.localComponent w).padicObject (hP w).1 (hP w).2)
    ((Q.localComponent w).padicObject (hQ w).1 (hQ w).2) ⟨eρ⟩ ⟨eτ⟩ ψ ν φ ξ
    (CuspidalPairPartialGamma.localGenericity K r T P w (hP w).1 (hP w).2 φ)
    (CuspidalPairPartialGamma.localGenericity K r U Q w (hQ w).1 (hQ w).2 φ) A B hA hB

set_option maxHeartbeats 1900000 in
private theorem twistFirstAfterPullback {r : ℕ} {T : CuspidalOperatorRealization K r}
    (P : CuspidalSpectralPresentation.{0,0} T) (w : FinitePlace K)
    (a : F.Carrier ≃+* w.adicCompletion K) (χ : HeckeCharacter K)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (e : ρ.Equiv ((P.localComponent w).representation.comp (Matrix.GeneralLinearGroup.map a.toRingHom))) :
    let κ := (χ.finiteComponent w).toMonoidHom.comp (Units.mapEquiv a.toMulEquiv).toMonoidHom
    Nonempty ((twist (κ.comp determinant) ρ).Equiv
      (((P.heckeDeterminantTwist χ).localComponent w).representation.comp
        (Matrix.GeneralLinearGroup.map a.toRingHom))) := by
  have hchar : (χ.finiteLocalDeterminant (r + 1) w).toMonoidHom =
      (χ.finiteComponent w).toMonoidHom.comp determinant := by
    ext g
    exact congrArg Units.val (HeckeCharacter.finiteLocalDeterminant_eq_finiteComponent_det χ (r + 1) w g)
  have d : (twist ((χ.finiteComponent w).toMonoidHom.comp determinant)
      (P.localComponent w).representation).Equiv ((P.heckeDeterminantTwist χ).localComponent w).representation := by
    rw [← hchar]
    exact ((P.localComponent w).heckeDeterminantTwistRepresentationEquiv χ).trans
      (P.heckeDeterminantTwistLocalComponentEquiv χ w).symm
  exact ⟨(pullbackDeterminantTwistEquiv a e (χ.finiteComponent w).toMonoidHom).trans
    (BinaryTensor.compEquiv d (Matrix.GeneralLinearGroup.map a.toRingHom))⟩

private theorem shiftPairCertificate {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) W)
    (ω κ : F.Carrierˣ →* ℂˣ) (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : SelfDualHaar F.canonicalTopologicalData ψ) {A : Polynomial ℂ}
    (hA : IsPadicRankLPolynomial F ψ ν.val ρ (twist (κ.comp determinant) τ) A) :
    IsPadicRankLPolynomial F ψ ν.val (twist (κ.comp determinant) (twist (ω.comp determinant) ρ))
      (twist (ω⁻¹.comp determinant) τ) A := by
  have h := (isPadicSymmetricLPolynomial_of_le (Nat.le_refl r)).mp (isPadicRankLPolynomial_succ.mp hA)
  have hm := (isPadicPairLPolynomial_twist_left_iff_right κ).mpr h
  have ht := (isPadicPairLPolynomial_twist ψ ν.val (twist (κ.comp determinant) ρ) τ ω A).mpr hm
  rw [twist_twist, mul_comm (ω.comp determinant), ← twist_twist] at ht
  exact isPadicRankLPolynomial_succ.mpr ((isPadicSymmetricLPolynomial_of_le (Nat.le_refl r)).mpr ht)

set_option maxHeartbeats 4200000 in
private theorem compareDistinguishedSelfPair {r : ℕ} {T Td : CuspidalOperatorRealization K r}
    (hTd : Td.realization.IsContragredientOf T.realization)
    (P : CuspidalSpectralPresentation.{0,0} T) (Pd : CuspidalSpectralPresentation.{0,0} Td)
    (hP : HasIrreducibleAdmissibleComponents P) (hPd : HasIrreducibleAdmissibleComponents Pd)
    (w : FinitePlace K) (a : F.Carrier ≃+* w.adicCompletion K) (ha : Continuous a) (ha' : Continuous a.symm)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) (hρ : ρ.IsIrreducible)
    (ht : F.canonicalTopologicalData.IsTempered ρ) (ω : F.Carrierˣ →* ℂˣ)
    (hω : IsOpen (ω.ker : Set F.Carrierˣ))
    (e : (twist (ω.comp determinant) ρ).Equiv
      ((P.localComponent w).representation.comp (Matrix.GeneralLinearGroup.map a.toRingHom)))
    (χ : HeckeCharacter K) (κ : F.Carrierˣ →* ℂˣ)
    (hκ : (χ.finiteComponent w).toMonoidHom.comp (Units.mapEquiv a.toMulEquiv).toMonoidHom = κ)
    (hopen : IsOpen (κ.ker : Set F.Carrierˣ)) (hunit : ∀ x, ‖(κ x : ℂ)‖ = 1)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : SelfDualHaar F.canonicalTopologicalData ψ)
    (A : Polynomial ℂ)
    (hA : IsPadicRankLPolynomial F ψ ν.val ρ (twist (κ.comp determinant) (smoothContragredient ρ)) A) :
    let D := standardSelfPairSetup hTd P Pd hP hPd
    A = (D.twistedChoice χ).lPolynomial w ∧
      ∀ x, ‖x‖ < 1 → ((D.twistedChoice χ).lPolynomial w).eval x ≠ 0 ∧
        ((D.twistedChoice χ).dualLPolynomial w).eval x ≠ 0 := by
  classical
  let J := F.canonicalTopologicalData
  let D := standardSelfPairSetup hTd P Pd hP hPd
  let φ := D.additive w
  let ξ : SelfDualHaar (padicField w).canonicalTopologicalData φ := ⟨D.measure w, D.measure_spec w⟩
  let δ := κ.comp (determinant (n := r + 1))
  have hδ : IsOpen (δ.ker : Set (GeneralLinear (r + 1) F.Carrier)) :=
    hopen.preimage (J.generalLinearDeterminant (r + 1)).continuous
  have hδunit (x : GeneralLinear (r + 1) F.Carrier) : ‖(δ x : ℂ)‖ = 1 := hunit (determinant x)
  have hκinv : (χ⁻¹.finiteComponent w).toMonoidHom.comp (Units.mapEquiv a.toMulEquiv).toMonoidHom = κ⁻¹ :=
    MonoidHom.ext fun x => congrArg Inv.inv (DFunLike.congr_fun hκ x)
  have ha₀ : @Continuous F.Carrier (padicField w).Carrier _ (padicField w).canonicalTopologicalData.topology a := by
    rw [← completion_topology_eq w]
    exact ha
  have ha₁ : @Continuous (padicField w).Carrier F.Carrier (padicField w).canonicalTopologicalData.topology _ a.symm := by
    rw [← completion_topology_eq w]
    exact ha'
  let : TopologicalSpace (padicField w).Carrier := (padicField w).canonicalTopologicalData.topology
  let : TopologicalSpace (GeneralLinear (r + 1) (padicField w).Carrier) :=
    (padicField w).canonicalGeneralLinearTopology (r + 1)
  let : IsTopologicalGroup (GeneralLinear (r + 1) (padicField w).Carrier) :=
    (padicField w).canonicalGeneralLinearTopologicalGroup (r + 1)
  let aG := fieldEquiv (r + 1) a ha₀ ha₁
  let ρd := smoothContragredient ρ
  let S := (P.localComponent w).representation
  let Sd := (Pd.localComponent w).representation
  obtain ⟨ed⟩ := cuspidalContragredientLocalCompatibility K r T Td hTd P Pd w
    (hP w).1 (hP w).2 (hPd w).1 (hPd w).2
  have hωdet : IsOpen ((ω.comp (determinant (n := r + 1))).ker : Set (GeneralLinear (r + 1) F.Carrier)) :=
    hω.preimage (J.generalLinearDeterminant (r + 1)).continuous
  have hωinv : (ω.comp (determinant (n := r + 1)))⁻¹ = ω⁻¹.comp determinant :=
    MonoidHom.ext fun _ => rfl
  have eDual : (twist (ω⁻¹.comp determinant) ρd).Equiv (Sd.comp aG.toMonoidHom) := by
    rw [← hωinv]
    exact (smoothContragredientTwistEquiv (ω.comp determinant) ρ hωdet).symm.trans
      ((smoothContragredientEquiv e.symm).trans
        ((smoothContragredientCompEquiv S aG).trans (BinaryTensor.compEquiv ed.symm aG.toMonoidHom)))
  have htw := twistFirstAfterPullback F P w a χ _ e
  dsimp only at htw
  rw [hκ] at htw
  obtain ⟨eχ⟩ := htw
  have htwd := twistFirstAfterPullback F Pd w a χ⁻¹ _ eDual
  dsimp only at htwd
  rw [hκinv] at htwd
  obtain ⟨eχd⟩ := htwd
  have eqF : A = (D.twistedChoice χ).lPolynomial w :=
    compareCuspidalPolynomial F (P.heckeDeterminantTwist χ) Pd
      (P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ hP) hPd w a ha ha'
      _ _ eχ eDual ψ ν φ ξ (shiftPairCertificate F ρ ρd ω κ ψ ν hA) (D.finiteData_specs χ w).1
  let B := SmoothRep.of ρ ht.isAdmissible.1
  have hid : ρd.IsIrreducible :=
    (B.isIrreducible_contragredient_iff (compactOpen_cofinal F J (r + 1)) ht.isAdmissible).mpr hρ
  have hinv : (κ⁻¹.comp (determinant (n := r + 1))) = δ⁻¹ := MonoidHom.ext fun _ => rfl
  have ht' : J.IsTempered (twist (κ⁻¹.comp determinant) ρ) := by
    rw [hinv]
    have hker : δ⁻¹.ker = δ.ker := by ext x; simp
    let := J.centralQuotientMeasurableSpace (r + 1)
    intro μ _
    exact isTemperedModCenter_unitaryTwist δ⁻¹ (hker ▸ hδ)
      (fun x => by simpa using hδunit x) μ (ht μ)
  let Adual := analyticTemperedLPolynomialData F ψ ν ρd (twist (κ⁻¹.comp determinant) ρ)
    hid ht.smoothContragredient ((isIrreducible_twist_iff _ _).mpr hρ) ht'
  have hω' : (ω⁻¹)⁻¹ = ω := MonoidHom.ext fun x => inv_inv (ω x)
  have eqD : Adual.polynomial = (D.twistedChoice χ).dualLPolynomial w :=
    compareCuspidalPolynomial F (Pd.heckeDeterminantTwist χ⁻¹) P
      (Pd.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ⁻¹ hPd) hP w a ha ha'
      _ _ eχd (by rw [hω']; exact e) ψ ν φ ξ
      (shiftPairCertificate F ρd ρ ω⁻¹ κ⁻¹ ψ ν (isPadicRankLPolynomial_succ.mpr Adual.spec))
      (D.finiteData_specs χ w).2.1
  have hAfree := (temperedSelfPairEulerRootRegion p F r V ρ hρ ht δ hδ hδunit ψ ν).1 A hA
  exact ⟨eqF, fun x hx => ⟨eqF ▸ hAfree x hx, eqD ▸ Adual.poleFree x hx⟩⟩

end LocalPair

set_option maxHeartbeats 500000 in
private theorem isUnramifiedCharacter_of_valued {K : Type} [Field K] [NumberField K]
    (w : FinitePlace K) (χ : (w.adicCompletion K)ˣ →* ℂˣ)
    (hχ : ∀ x : (w.adicCompletion K)ˣ, Valued.v (x : w.adicCompletion K) = 1 → χ x = 1) :
    (padicField w).canonicalTopologicalData.IsUnramifiedCharacter χ := by
  let F := padicField w
  let T := F.canonicalTopologicalData
  let : Algebra (Padic (residuePrime w)) F.Carrier := F.algebra
  let : FiniteDimensional (Padic (residuePrime w)) F.Carrier := F.finiteDimensional
  intro x hx
  apply hχ
  apply (valued_isEquiv w).eq_one_iff_eq_one.mpr
  rw [← NNReal.coe_eq_one, PadicField.canonicalValuation_coe]
  have h := congrArg (fun z : ℝ≥0ˣ => ((z : ℝ≥0) : ℝ)) (MonoidHom.mem_ker.mp hx)
  change T.normalizedAbs (x : F.Carrier) = 1 at h
  rw [T.normalizedAbs_eq_canonicalNorm_pow_degree] at h
  have hNonneg : 0 ≤ F.canonicalNorm (x : F.Carrier) := by
    rw [← PadicField.canonicalValuation_coe]
    exact NNReal.coe_nonneg _
  exact (pow_eq_one_iff_of_nonneg hNonneg
    (Module.finrank_pos (R := Padic (residuePrime w)) (M := F.Carrier)).ne').mp h

private theorem isOpen_ker_completionUnramified {K : Type} [Field K] [NumberField K]
    (w : FinitePlace K) (χ : (w.adicCompletion K)ˣ →* ℂˣ)
    (hχ : (padicField w).canonicalTopologicalData.IsUnramifiedCharacter χ) :
    IsOpen (χ.ker : Set (w.adicCompletion K)ˣ) := by
  let T := (padicField w).canonicalTopologicalData
  have h : @IsOpen (w.adicCompletion K)ˣ (@Units.instTopologicalSpaceUnits _ T.topology _) χ.ker := by
    let : TopologicalSpace ((padicField w).Carrier) := T.topology
    let : ValuativeRel ((padicField w).Carrier) := T.valuativeRel
    let : IsNonarchimedeanLocalField ((padicField w).Carrier) := T.localField
    exact Subgroup.isOpen_mono hχ T.isOpen_ker_normalizedAbsUnits
  rwa [← completion_topology_eq w] at h

/-- The local self-pair identity follows from ordinary globalization, cyclic
cuspidal lifting, local lift uniqueness and the completed pair equation. -/
def SigmaLiftSelfPairFromGlobalizationStatement : Prop :=
  GeneralLinearDiscreteSeriesGlobalizationStatement.{0,uV,0} →
  CuspidalCyclicBaseChangeLiftAnyDegreeStatement.{0,0,0} →
  SigmaLiftUniquenessStatement.{u,v,uV,uW,0} →
  CuspidalPairGlobalFunctionalEquationStatement.{0,0} →
  SigmaLiftSelfPairLFactorStatement.{u,v,uV,uW}

set_option maxHeartbeats 8800000 in
/-- Localize the cuspidal equations at the unique upper completion and
transport the original distributional lift and its pair certificates. -/
theorem sigmaLiftSelfPairLFactor_of_globalization
    : SigmaLiftSelfPairFromGlobalizationStatement.{u,v,uV,uW} := by
  classical
  intro hGlobal hBaseChange hUnique hEquation p _ F E _ _
  let TF := F.canonicalTopologicalData
  let TE := E.canonicalTopologicalData
  let := TF.topology
  let := TE.topology
  let := TF.valuativeRel
  let := TE.valuativeRel
  let := TF.localField
  let := TE.localField
  let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  intro _ σ l f n hcyc hf hn V _ _ W _ _ π hπ ρE hρE J c hi hsq hσd hlift
    ψF νF ψE νE X hX Q_E Q_F hQE hQF
  let : FiniteDimensional F.Carrier E.Carrier := hcyc.1
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  by_cases hr : r = 0
  · subst r
    exact rankOneSelfPairLFactorComparison p F E f hf V W π ρE hπ hi hρE hσd.2.1
      ψF νF ψE νE X hX Q_E Q_F hQE hQF
  by_cases hl : l = 1
  · subst l
    exact degreeOneSigmaSelfPairEuler p F E σ f r hcyc hf V W π hπ ρE hρE J c
      hi hσd.2.1 hlift ψF νF ψE νE X hX Q_E Q_F hQE hQF
  obtain ⟨K, L, fK, nK, fL, nL, aKL, gKL, cKL, cK, cL, σ₀, hcyc₀, hInf, v₀, w₀, hw₀, a, b,
    ha, ha', hb, hb', hab, hσb, v₁, v₂, h₁, h₂, h₁₂, hs₁, hs₂⟩ :=
    cyclicGlobalizationWithSplitPlaces F.Carrier E.Carrier σ l hcyc
  let Kv := v₀.adicCompletion K
  let Lw := w₀.1.adicCompletion L
  let : ValuativeRel Kv := (topologicalData v₀).valuativeRel
  let : IsNonarchimedeanLocalField Kv := (topologicalData v₀).localField
  let : ValuativeRel Lw := (topologicalData w₀.1).valuativeRel
  let : IsNonarchimedeanLocalField Lw := (topologicalData w₀.1).localField
  let := LocalFieldTopology.generalLinear_t2Space Kv (r + 1)
  let := LocalFieldTopology.generalLinear_locallyCompactSpace Kv (r + 1)
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace Kv (r + 1)
  let := LocalFieldTopology.generalLinear_t2Space Lw (r + 1)
  let := LocalFieldTopology.generalLinear_locallyCompactSpace Lw (r + 1)
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace Lw (r + 1)
  let aG := fieldEquiv (r + 1) a ha ha'
  let bG := fieldEquiv (r + 1) b hb hb'
  let R := π.comp aG.symm.toMonoidHom
  let S := ρE.comp bG.symm.toMonoidHom
  let eR : π.Equiv (R.comp aG.toMonoidHom) :=
    equivOfRepresentationEq (MonoidHom.ext fun g => congrArg π (aG.symm_apply_apply g).symm)
  let eS : ρE.Equiv (S.comp bG.toMonoidHom) :=
    equivOfRepresentationEq (MonoidHom.ext fun g => congrArg ρE (bG.symm_apply_apply g).symm)
  have hRsq : JacquetLanglands.IsSquareIntegrable R := by
    let := JacquetLanglands.centralQuotientMeasurableSpace Kv (r + 1)
    let := JacquetLanglands.centralQuotientBorelSpace Kv (r + 1)
    let := JacquetLanglands.centralQuotientMeasurableSpace F.Carrier (r + 1)
    let := JacquetLanglands.centralQuotientBorelSpace F.Carrier (r + 1)
    intro μ _
    exact isSquareIntegrableModCenter_comp_continuousMulEquiv π aG.symm μ (hsq _)
  obtain ⟨T, P, hT, hP, hPs₁, hPs₂, ω, hω, -, ⟨eP⟩⟩ :=
    hGlobal K v₀ v₁ v₂ h₁.symm h₂.symm h₁₂ r (Nat.pos_of_ne_zero hr)
      V R hRsq.isAdmissible ((isIrreducible_comp_continuousMulEquiv_iff π aG.symm).mpr hi) hRsq
  obtain ⟨U, Q, -, hWeak, -, -, hQlift, hQ⟩ :=
    hBaseChange K L σ₀ l hcyc₀ hInf r T P hT hP v₁ v₂ h₁₂ hs₁ hs₂ hPs₁ hPs₂
  have hTensor : IsLiftAtDistinguishedTensor w₀ hw₀ σ₀ l (P.localComponent v₀) (Q.localComponent w₀.1) :=
    hQlift v₀ w₀ hw₀
  obtain ⟨J₀, c₀, hLift₀⟩ := distinguishedTensorLiftTransport K L r v₀ w₀ hw₀ σ₀ l
    (P.localComponent v₀) (Q.localComponent w₀.1) (hP v₀).2 (hQ w₀.1).2 hTensor
  have hUnr := isUnramifiedCharacter_of_valued v₀ ω hω
  have hωOpen := isOpen_ker_completionUnramified v₀ ω hUnr
  let μ : Quasicharacter Kv := ⟨ω, CuspidalSupport.NormalHecke.continuous_of_isOpen_ker ω hωOpen⟩
  let η := ω.comp (normUnits Kv Lw)
  obtain ⟨eQ⟩ := distinguishedSigmaLiftMatch hUnique F.Carrier E.Carrier Kv Lw σ
    (uniquePlaceCompletionAutEquiv w₀ hw₀ σ₀) l (r + 1) hcyc a b ha ha' hb hb'
    (FiniteExtension.continuous_completionMap v₀ w₀.1) hab hσb V W π ρE hi hσd.2.1 hπ hρE J c
    hlift R S ⟨eR⟩ ⟨eS⟩ μ (P.localComponent v₀).Space (Q.localComponent w₀.1).Space
    (P.localComponent v₀).representation (Q.localComponent w₀.1).representation (hQ w₀.1).1
    ⟨eP⟩ (hP v₀).2 (hQ w₀.1).2 J₀ c₀ hLift₀
  obtain ⟨Td, Pd, hTd, hPd⟩ := exists_cuspidalContragredient_presentation.{0,0} K T
  obtain ⟨Ud, Qd, hUd, hQd⟩ := exists_cuspidalContragredient_presentation.{0,0} L U
  let D := standardSelfPairSetup hTd P Pd hP hPd
  let B := standardSelfPairSetup hUd Q Qd hQ hQd
  have hWeakDual := contragredient_weakBaseChange hTd hUd P Pd Q Qd hP hPd hQ hQd hWeak
  let I := (L ≃ₐ[K] L) →* ℂˣ
  let : Fintype I := Fintype.ofFinite _
  obtain ⟨χ, iX, -, -, -, hχ, hrestriction⟩ := distinguishedNormCharacters K L v₀ w₀ hw₀
    F.Carrier E.Carrier a b (RingHom.ext fun x => (hab x).symm) X hX
  let aU := Units.mapEquiv a.toMulEquiv
  let bU := Units.mapEquiv b.toMulEquiv
  let ωF := ω.comp aU.toMonoidHom
  let ωE := η.comp bU.toMonoidHom
  have hηOpen : IsOpen (η.ker : Set Lwˣ) :=
    isOpen_ker_completionUnramified w₀.1 η (completion_unramified_comp_norm v₀ w₀ ω hUnr)
  have hωF : IsOpen (ωF.ker : Set F.Carrierˣ) := hωOpen.preimage (ha.units_map a.toMonoidHom)
  have hωE : IsOpen (ωE.ker : Set E.Carrierˣ) := hηOpen.preimage (hb.units_map b.toMonoidHom)
  let eF := (pullbackDeterminantTwistEquiv a eR ω).trans (BinaryTensor.compEquiv eP aG.toMonoidHom)
  let eE := (pullbackDeterminantTwistEquiv b eS η).trans (BinaryTensor.compEquiv eQ bG.toMonoidHom)
  have htF : TF.IsTempered π :=
    (isTemperedRep_iff_isTempered TF π).mp (isTemperedRep_of_isSquareIntegrable hsq)
  have htE : TE.IsTempered ρE := (isTemperedRep_iff_isTempered TE ρE).mp hσd.2.2.1
  have hκOpen (i : I) : IsOpen ((iX i).val.ker : Set F.Carrierˣ) := by
    let : NontriviallyNormedField F.Carrier := F.canonicalNormedField
    let : CompleteSpace F.Carrier := inferInstance
    exact ((hX _).mp (iX i).property).isOpen_ker
  have hF (i : I) := compareDistinguishedSelfPair F hTd P Pd hP hPd v₀ a ha ha'
    π hi htF ωF hωF eF (χ i) (iX i).val (hχ i).symm (hκOpen i)
    ((hX _).mp (iX i).property).norm_eq_one ψF νF (Q_F (iX i)) (hQF (iX i))
  have hone : ((1 : HeckeCharacter L).finiteComponent w₀.1).toMonoidHom.comp bU.toMonoidHom = 1 :=
    MonoidHom.ext fun _ => rfl
  have hcertE : IsPadicRankLPolynomial E ψE νE.val ρE
      (twist ((1 : E.Carrierˣ →* ℂˣ).comp determinant) (smoothContragredient ρE)) Q_E := by
    simpa only [MonoidHom.one_comp, twist_one] using hQE
  have hE := compareDistinguishedSelfPair E hUd Q Qd hQ hQd w₀.1 b hb hb' ρE hσd.2.1 htE
    ωE hωE eE 1 1 hone (by simp) (by simp) ψE νE Q_E hcertE
  have hw : RelativeWeilEngine.placesAbove L v₀ = {w₀.1} := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, -, rfl⟩ := Finset.mem_map.mp hz
      exact Finset.mem_singleton.mpr (congrArg Subtype.val (hw₀ w))
    · intro hz
      obtain rfl := Finset.mem_singleton.mp hz
      exact Finset.mem_map.mpr ⟨w₀, Finset.mem_univ _, rfl⟩
  have hEq := cuspidalPairDistinguishedNormEuler D B I χ v₀ w₀ hEquation hWeak hWeakDual hw
    hrestriction (fun i => (hF i).2) hE.2
  have hcardF := (LocalFieldData.ofInstances F.Carrier).residueCardinality_of_continuous_ringEquiv
    (LocalFieldData.ofInstances Kv) a ha ha'
  have hcardE := (LocalFieldData.ofInstances E.Carrier).residueCardinality_of_continuous_ringEquiv
    (LocalFieldData.ofInstances Lw) b hb hb'
  have hdeg : f = w₀.1.asIdeal.inertiaDeg (𝓞 K) := hf.unique (by
    change (LocalFieldData.ofInstances E.Carrier).residueCardinality =
      (LocalFieldData.ofInstances F.Carrier).residueCardinality ^ _
    rw [← hcardF, ← hcardE]
    change (padicField w₀.1).canonicalTopologicalData.residueCardinality =
      (padicField v₀).canonicalTopologicalData.residueCardinality ^ _
    rw [canonicalResidueCardinality_eq_absNorm, canonicalResidueCardinality_eq_absNorm]
    exact (Ideal.absNorm_pow_inertiaDeg v₀.asIdeal w₀.1.asIdeal).symm)
  rw [hdeg, hE.1]
  exact hEq.trans (Fintype.prod_equiv iX _ Q_F (fun i => (hF i).1.symm))

end Langlands.BaseChange
