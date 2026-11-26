import Langlands.Automorphic.HeckeDeterminantTwistSupercuspidalProof
import Langlands.BaseChange.CharZeroRankOneSigmaLift
import Langlands.BaseChange.CharZeroTraceConductorPremises
import Langlands.BaseChange.CuspidalSigmaLiftTraceEpsilonFactors
import Langlands.BaseChange.DistinguishedNormCharacters
import Langlands.BaseChange.DistinguishedStandardTwistTransport
import Langlands.BaseChange.SupercuspidalStandardFactorsAtCompletion
import Langlands.Representation.Conductor.FieldEquivTransport

/-! # The conductor formula from completed standard equations -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v uV uW

namespace Langlands.BaseChange

open Automorphic Automorphic.ConstantFunctions Global Global.AdelicFunctoriality
open Global.CompletionPadic Global.CuspidalPairFunctionalEquation Global.HeckeFunctionalEquation
open Global.FunctionalEquationComparison GeneralLinear
open scoped BigOperators FiniteExtension

section FiniteFactorData

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [CompactSpace (AdeleQuotient K)] [CompactSpace (AdeleQuotient L)] {r : ℕ}
  (v₀ : FinitePlace K) (w₀ : FinitePlace L)
  {T : CuspidalOperatorRealization K r} {U : CuspidalOperatorRealization L r}
  (D : CuspidalSpectralPresentation.{0, 0} T) (Q : CuspidalSpectralPresentation.{0, 0} U)
  (hD : HasIrreducibleAdmissibleComponents D) (hQ : HasIrreducibleAdmissibleComponents Q)

/-- The finite factor conditions for the global comparison. At the distinguished
upper place the forward and reflected dual roots are separated. At the other
places the grouped forward and dual Euler values and the positive epsilon
bases agree. -/
def HasGlobalStandardFactorComparisons : Prop :=
  ∀ (Td : CuspidalOperatorRealization K r) (Ud : CuspidalOperatorRealization L r),
    Td.realization.IsContragredientOf T.realization → Ud.realization.IsContragredientOf U.realization →
  ∀ (Dd : CuspidalSpectralPresentation.{0, 0} Td) (Qd : CuspidalSpectralPresentation.{0, 0} Ud)
    (hDd : HasIrreducibleAdmissibleComponents Dd) (hQd : HasIrreducibleAdmissibleComponents Qd)
    (χ : ((L ≃ₐ[K] L) →* ℂˣ) → HeckeCharacter K),
    (∀ i, (χ i).normComp (L := L) = 1) →
    (∀ (p : FinitePlace K) (w : FinitePlacesAbove L p) (κ : (p.adicCompletion K)ˣ →* ℂˣ),
      (IsNormTrivial (w.1.adicCompletion L) κ ↔ ∃ i, ((χ i).finiteComponent p).toMonoidHom = κ) ∧
      (IsNormTrivial (w.1.adicCompletion L) κ →
        Nat.card {i // ((χ i).finiteComponent p).toMonoidHom = κ} =
          Nat.card (FinitePlacesAbove L p))) →
    let C := rankOneSpectralPresentation.{0, 0} K
    let B := rankOneSpectralPresentation.{0, 0} L
    let hC := rankOneSpectralPresentation_hasIrreducibleAdmissibleComponents.{0, 0} K
    let hB := rankOneSpectralPresentation_hasIrreducibleAdmissibleComponents.{0, 0} L
    letI := Fintype.ofFinite ((L ≃ₐ[K] L) →* ℂˣ)
    ∀ (cF : ∀ i, FinitePairFactorChoice (standardGlobalAdditiveCharacter K)
        (D.heckeDeterminantTwist (χ i)) C (Dd.heckeDeterminantTwist (χ i)⁻¹) C
        (D.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents (χ i) hD) hC
        (Dd.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents (χ i)⁻¹ hDd) hC)
      (cE : FinitePairFactorChoice (standardGlobalAdditiveCharacter L) Q B Qd B hQ hB hQd hB),
      (∀ x : ℂ, x ≠ 0 → (cE.lPolynomial w₀).eval x = 0 →
        (cE.dualLPolynomial w₀).eval ((residueCardinality w₀ : ℂ)⁻¹ / x) ≠ 0) ∧
      ∀ p ≠ v₀,
        (∀ z, (∏ i, (cF i).finiteL p z) = ∏ w ∈ RelativeWeilEngine.placesAbove L p, cE.finiteL w z) ∧
        (∀ z, (∏ i, (cF i).finiteDualL p z) = ∏ w ∈ RelativeWeilEngine.placesAbove L p, cE.finiteDualL w z) ∧
        finiteEpsilonBase Finset.univ (fun _ : (L ≃ₐ[K] L) →* ℂˣ => residueCardinality p)
          (fun i => (cF i).epsilon p) =
          finiteEpsilonBase (RelativeWeilEngine.placesAbove L p) residueCardinality cE.epsilon

end FiniteFactorData

section LocalRepresentationInstances

local instance completedConductorRationalGroup (K : Type) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions K n) := Submodule.addCommGroup _
local instance completedConductorContinuousGroup (K : Type) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions K n) := Submodule.addCommGroup _
local instance completedConductorSmoothGroup (K : Type) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions K n) := Submodule.addCommGroup _
local instance completedConductorFormsGroup (K : Type) [Field K] [NumberField K] (n : ℕ) :
    AddCommGroup (AutomorphicForms K n) := Submodule.addCommGroup _
local instance completedConductorLocalGroup {K : Type} [Field K] [NumberField K]
    {n : ℕ} {p : FinitePlace K} (D : LocalRealization K n p) :
    AddCommGroup D.Space := Submodule.addCommGroup _

/-- Above rank one, the global presentations realize the specified lower and
upper local actions up to unramified twists at a pair of compatible
completions. They satisfy the finite factor conditions of the global comparison. -/
def CuspidalSigmaLiftGlobalFactorDataStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l : ℕ), IsCyclicAlgebra σ l →
    ∀ (k : ℕ), 0 < k →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear (k + 1) F) V)
      (hπ : IsAdmissible π), GeneralLinear.IsSupercuspidal π → π.IsIrreducible →
    ∀ (s k₁ : ℕ) (h : s * (k₁ + 1) = k + 1)
      (W₁ : Type uW) [AddCommGroup W₁] [Module ℂ W₁]
      (P₁ : Representation ℂ (GeneralLinear (k₁ + 1) E) W₁),
      GeneralLinear.IsSupercuspidal P₁ → P₁.IsIrreducible →
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
    ∃ (p : FinitePlace K) (w : FinitePlacesAbove L p)
      (a : F ≃+* p.adicCompletion K) (b : E ≃+* w.1.adicCompletion L),
      (∀ w' : FinitePlacesAbove L p, w' = w) ∧
      Continuous a ∧ Continuous a.symm ∧ Continuous b ∧ Continuous b.symm ∧
      (algebraMap (p.adicCompletion K) (w.1.adicCompletion L)).comp a.toRingHom =
        b.toRingHom.comp (algebraMap F E) ∧
    ∃ (T : CuspidalOperatorRealization K k) (U : CuspidalOperatorRealization L k)
      (D : CuspidalSpectralPresentation.{0, 0} T) (Q : CuspidalSpectralPresentation.{0, 0} U)
      (hD : HasIrreducibleAdmissibleComponents D) (hQ : HasIrreducibleAdmissibleComponents Q)
      (R : Representation ℂ (GeneralLinear (k + 1) (p.adicCompletion K)) V)
      (S : Representation ℂ (GeneralLinear (k + 1) (w.1.adicCompletion L)) W)
      (μ : (p.adicCompletion K)ˣ →* ℂˣ) (η : (w.1.adicCompletion L)ˣ →* ℂˣ),
      (padicField p).canonicalTopologicalData.IsUnramifiedCharacter μ ∧
      (padicField w.1).canonicalTopologicalData.IsUnramifiedCharacter η ∧
      Nonempty (π.Equiv (R.comp (Matrix.GeneralLinearGroup.map a.toRingHom))) ∧
      Nonempty (P.Equiv (S.comp (Matrix.GeneralLinearGroup.map b.toRingHom))) ∧
      Nonempty ((twist (μ.comp determinant) R).Equiv (D.localComponent p).representation) ∧
      Nonempty ((twist (η.comp determinant) S).Equiv (Q.localComponent w.1).representation) ∧
      (D.localComponent p).IsSupercuspidal ∧ HasGlobalStandardFactorComparisons p w.1 D Q hD hQ

private theorem placesAbove_eq_singleton {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] {p : FinitePlace K} (w : FinitePlacesAbove L p)
    (hw : ∀ w' : FinitePlacesAbove L p, w' = w) :
    RelativeWeilEngine.placesAbove L p = {w.1} := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_map.mp hx
    rw [hw y]
    exact Finset.mem_singleton_self _
  · intro hx
    rw [Finset.mem_singleton.mp hx]
    exact Finset.mem_map.mpr ⟨w, Finset.mem_univ _, rfl⟩

private theorem firstFixedLevel_eq_of_newvector {F : Type*} [Field F] [ValuativeRel F] {r : ℕ}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GeneralLinear (r + 1) F) V} {n : ℕ}
    (h : Conductor.IsNewvectorConductor π n) :
    Conductor.firstFixedLevel π = (n : WithTop ℕ) := by
  have hlevel : Conductor.HasNewvectorLevel π := ⟨n, h.1⟩
  rw [Conductor.firstFixedLevel_of_hasNewvectorLevel π hlevel,
    (Conductor.newvectorConductor_eq_iff π hlevel n).mpr h]

/-- The completed global functional equations and the global factor data
in ranks greater than one imply the four-universe conductor identity. -/
def CuspidalSigmaLiftConductorFromCompletedEquationsStatement : Prop :=
  CuspidalPairGlobalFunctionalEquationStatement.{0, 0} →
    CuspidalSigmaLiftGlobalFactorDataStatement.{u, v, uV, uW} →
      CuspidalSigmaLiftConductorStatement.{u, v, uV, uW}

set_option maxHeartbeats 4500000 in
theorem cuspidalSigmaLiftConductorFromCompletedEquations :
    CuspidalSigmaLiftConductorFromCompletedEquationsStatement.{u, v, uV, uW} := by
  classical
  intro hFE hdata F _ _ _ _ _ E _ _ _ _ _ _ σ l hcyc k V _ _ π hπ hπs hπi
    s k₁ hrank W₁ _ _ P₁ hP₁s hP₁i W _ _ P hP horbit A c hlift f d hf hd X hX
  by_cases hk : k = 0
  · subst k
    exact cuspidalSigmaLiftConductorRankOne F E σ l hcyc V π hπ hπs hπi
      s k₁ hrank W₁ P₁ hP₁s hP₁i W P hP horbit A c hlift f d hf hd X hX
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  let : FiniteDimensional F E := hcyc.1
  obtain ⟨K, L, _, _, _, _, _, _, _, _, _,
    p, w, a, b, hw, ha, ha', hb, hb', hab, T, U, D, Q, hD, hQ, R, S, μ, η,
    hμ, hη, ⟨eπ⟩, ⟨eP⟩, ⟨eR⟩, ⟨eS⟩, hDs, hloc⟩ :=
    hdata F E σ l hcyc k hkpos V π hπ hπs hπi s k₁ hrank W₁ P₁ hP₁s hP₁i
      W P hP horbit A c hlift
  let I := (L ≃ₐ[K] L) →* ℂˣ
  obtain ⟨χ, iX, _, hnorm, hcard, hindex, hrestr⟩ := distinguishedNormCharacters K L
    p w hw F E a b hab X hX
  let : Fintype I := Fintype.ofFinite I
  have hI : Fintype.card I = Module.finrank K L := (Nat.card_eq_fintype_card (α := I)).symm.trans hcard
  obtain ⟨Td, Dd, ht, hDd⟩ := exists_cuspidalContragredient_presentation.{0, 0} K T
  obtain ⟨Ud, Qd, hu, hQd⟩ := exists_cuspidalContragredient_presentation.{0, 0} L U
  obtain ⟨cF, cE, hc⟩ := standardTwistDistinguishedEpsilon hFE K L k I hI p w.1
    (placesAbove_eq_singleton w hw) T Td U Ud ht hu D Dd Q Qd hD hDd hQ hQd χ (by
      intro cF cE
      refine ⟨fun i => ?_, hloc Td Ud ht hu Dd Qd hDd hQd χ
        (fun i => (hnorm (χ i)).mpr ⟨i, rfl⟩) hrestr cF cE⟩
      exact supercuspidalStandardFactorsAtCompletion K k hkpos _ _
        (ht.heckeDeterminantTwist_inv (χ i))
        (D.heckeDeterminantTwist (χ i)) (Dd.heckeDeterminantTwist (χ i)⁻¹)
        (D.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents (χ i) hD)
        (Dd.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents (χ i)⁻¹ hDd)
        (standardGlobalAdditiveCharacter K) (cF i) p
        (heckeDeterminantTwistSupercuspidal K T D (χ i) p hDs))
  have ha₀ : @Continuous F (padicField p).Carrier ‹TopologicalSpace F›
      (padicField p).canonicalTopologicalData.topology a := by
    rw [← completion_topology_eq p]
    exact ha
  have ha₁ : @Continuous (padicField p).Carrier F (padicField p).canonicalTopologicalData.topology
      ‹TopologicalSpace F› a.symm := by
    rw [← completion_topology_eq p]
    exact ha'
  have hb₀ : @Continuous E (padicField w.1).Carrier ‹TopologicalSpace E›
      (padicField w.1).canonicalTopologicalData.topology b := by
    rw [← completion_topology_eq w.1]
    exact hb
  have hb₁ : @Continuous (padicField w.1).Carrier E (padicField w.1).canonicalTopologicalData.topology
      ‹TopologicalSpace E› b.symm := by
    rw [← completion_topology_eq w.1]
    exact hb'
  let ψF := standardCompletionAdditivePullback p a ha₀
  let ψE := standardCompletionAdditivePullback w.1 b hb₀
  let νF := standardCompletionSelfDualPullback p a ha₀ ha₁
  let νE := standardCompletionSelfDualPullback w.1 b hb₀ hb₁
  have htrace := standardCompletionAdditivePullback_trace p w a b ha₀ hb₀ hab
  obtain ⟨aF, aB, eF, eB, eE, heF, heB, heE⟩ := cuspidalSigmaLiftCharZeroEpsilonFactors
    F E σ k s k₁ hrank π hπi hπs P₁ hP₁i hP₁s P horbit X (fun κ hκ => (hX κ).mp hκ)
    ψF ψE νF νE
  have hcomp := distinguishedStandardTwistTransport p w.1 D Dd Q Qd hD hDd hQ hQd χ cF cE
    a b ha₀ ha₁ hb₀ hb₁ π P R S μ η X iX hμ hη eπ eP eR eS hindex hc eF eE
    (fun κ hκ => (heF κ hκ).1) heE.1
  let TF := LocalFieldData.ofInstances F
  let TE := LocalFieldData.ofInstances E
  have hsum := hcomp.sum_eq TF.residueCardinality_gt_one hf
  have hcardX := normTrivialCount F E σ l hcyc X hX
  have hcond := traceAdditiveConductorFormula F E f d hf hd ψF ψE htrace
  rw [hcyc.2.1, ← hcardX] at hcond
  have hnew (i : Fin s) : Conductor.IsNewvectorConductor P₁ (aB i) := by
    let τ := σ ^ (i : ℕ)
    exact (Conductor.isNewvectorConductor_comp_fieldEquiv_iff τ.toRingEquiv
      (IsModuleTopology.continuous_of_linearMap τ.toLinearMap)
      (IsModuleTopology.continuous_of_linearMap τ.symm.toLinearMap) P₁ (aB i)).mp (heB i).2.1
  have hs : 0 < s := Nat.pos_of_ne_zero fun hs => by simp [hs] at hrank
  let i₀ : Fin s := ⟨0, hs⟩
  let a₁ := aB i₀
  have hB (i : Fin s) : aB i = a₁ := (hnew i).unique (hnew i₀)
  have hprod : EpsilonMonomialProductComparison TE.residueCardinality TE.residueCardinality
      Finset.univ eB eE := ⟨1, fun z => by simpa using heE.2 z⟩
  have hsumE := hprod.sum_eq TE.residueCardinality_gt_one (pow_one _).symm
  have hF : ∑ κ ∈ X, (eF κ).2 =
      ∑ κ ∈ X, (aF κ : ℤ) + (X.card : ℤ) * (((k + 1 : ℕ) : ℤ) * TF.additiveConductor ψF) := by
    rw [Finset.sum_congr rfl (fun κ hκ => (heF κ hκ).2.2),
      Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hE : eE.2 = (s : ℤ) * a₁ + ((k + 1 : ℕ) : ℤ) * TE.additiveConductor ψE := by
    have hr : (s : ℤ) * ((k₁ + 1 : ℕ) : ℤ) = ((k + 1 : ℕ) : ℤ) := by exact_mod_cast hrank
    simp only [Nat.cast_one, one_mul] at hsumE
    rw [← hsumE]
    simp only [(fun i => (heB i).2.2), hB, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_add, ← mul_assoc, hr, TE]
  have hint : ∑ κ ∈ X, (aF κ : ℤ) =
      (f : ℤ) * ((s : ℤ) * a₁ + ((k + 1 : ℕ) : ℤ) * d) := by
    rw [hF, hE] at hsum
    linear_combination hsum + ((k + 1 : ℕ) : ℤ) * hcond
  have hnat : ∑ κ ∈ X, aF κ = f * (s * a₁ + (k + 1) * d) := by exact_mod_cast hint
  rw [Finset.sum_congr rfl (fun κ hκ => firstFixedLevel_eq_of_newvector (heF κ hκ).2.1),
    firstFixedLevel_eq_of_newvector (hnew i₀)]
  exact_mod_cast hnat

end LocalRepresentationInstances

end Langlands.BaseChange
