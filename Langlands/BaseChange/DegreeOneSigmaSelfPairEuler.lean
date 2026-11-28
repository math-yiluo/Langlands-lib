import Langlands.BaseChange.ConcordanceConjugation
import Langlands.BaseChange.ExactNormAssociatedMeasure
import Langlands.BaseChange.SigmaLiftSelfPairLFactorStatement
import Langlands.BaseChange.TwistedCharacterSeparation
import Langlands.BaseChange.TwistedLocalGroupTransport
import Langlands.Correspondence.AssemblyRankOne
import Langlands.Global.Factors.DistinguishedFiniteStandardEpsilon
import Langlands.Representation.RankinSelberg.FieldTransport.LocalFieldLPolynomial
import Langlands.Representation.RankinSelberg.StableTwist.GammaCharacterChange
import Langlands.Representation.Smooth.Transfer.GroupEquivalence

/-! # The self-pair Euler identity for a degree-one sigma-lift -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v uV uW

namespace Langlands.BaseChange

open GeneralLinear HarmonicAnalysis JacquetLanglands MeasureTheory QuotientIntegration RankinSelberg TraceFormula
open Global.CuspidalPairFunctionalEquation LocalClassField
open LocalFactor.PadicAbelian (SelfDualHaar)
open scoped BigOperators

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

section DegreeOne

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
  {n : ℕ} {σ : E ≃ₐ[F] E}

private theorem cyclicNorm_one_term (δ : GeneralLinear n E) : cyclicNorm σ 1 δ = δ := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, cyclicNorm_succ, cyclicNorm_zero, pow_zero,
    entrywiseAut_one_apply, one_mul]

variable [TopologicalSpace F] [TopologicalSpace E] [IsTopologicalRing F] [IsTopologicalRing E]
  [ValuativeRel F] [IsNonarchimedeanLocalField F] [IsModuleTopology F E]
  [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
  [SecondCountableTopology (GeneralLinear n E)]
  [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
  [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]

set_option maxHeartbeats 550000 in
private theorem degreeOne_concordance (hcyc : IsCyclicAlgebra σ 1)
    (e : GeneralLinear n F ≃ₜ* GeneralLinear n E)
    (he : ∀ g, e g = baseChange F E n g)
    (μ : Measure (GeneralLinear n F)) [μ.IsHaarMeasure]
    (φ : GeneralLinear n E → ℂ) :
    letI := e.isHaarMeasure_map μ
    AreConcordant σ 1 μ (μ.map e) φ (φ ∘ e) := by
  let := e.isHaarMeasure_map μ
  have hσ : σ = 1 := by simpa only [pow_one] using hcyc.pow_eq_one
  have hθ (g : GeneralLinear n F) : e ((MonoidHom.id _) g) = entrywiseAut σ n (e g) := by
    rw [hσ, entrywiseAut_one_apply, MonoidHom.id_apply]
  have hbase : Measurable (baseChange F E n) := by
    rw [show (baseChange F E n : GeneralLinear n F → GeneralLinear n E) = e from
      (funext he).symm]
    exact e.continuous.measurable
  constructor
  · intro γ _ hn
    exact (hn ⟨e γ, 1, by rw [inv_one, one_mul, mul_one, cyclicNorm_one_term, he]⟩).elim
  · intro δ γ _ hγ
    apply concordAt_of_conj_of_cyclicNorm_eq hcyc.pow_eq_one hbase δ γ 1
    intro δ' hn
    simp only [inv_one, one_mul, mul_one, cyclicNorm_one_term, ← he] at hn ⊢
    subst δ'
    have hn : cyclicNorm σ 1 (e γ) = baseChange F E n γ := by rw [cyclicNorm_one_term, he]
    let hH := map_mem_twistedCentralizer_iff e (MonoidHom.id _) (entrywiseAut σ n) hθ γ
    intro μδ _ _ μγ _ _ νδ νγ hνδ hνγ hμ
    have hsub : (exactNormCentralizerEquiv hcyc hγ hn : glCentralizer γ → sigmaCentralizer σ n (e γ)) =
        subgroupEquiv e hH := by
      funext x
      exact Subtype.ext ((exactNormCentralizerEquiv_apply_val hcyc hγ hn x).trans (he x.val).symm)
    have hμ' := (isAssociatedMeasure_iff_map_exactNormCentralizerEquiv hcyc hγ hn μδ μγ).mp hμ
    rw [hsub] at hμ'
    let : BorelSpace (sigmaCentralizer σ n (e γ)) := Subtype.borelSpace _
    let : BorelSpace (glCentralizer γ) := Subtype.borelSpace _
    have hν' := (isCompatible_map_iff e hH μ μγ (μ.map e) μδ rfl hμ' νγ).mpr hνγ
    have hclosed : IsClosed (sigmaCentralizer σ n (e γ) : Set (GeneralLinear n E)) :=
      isClosed_twistedCentralizer (entrywiseAut σ n) (by rw [hσ]; simpa only [entrywiseAut_one_apply]
        using (continuous_id' : Continuous (fun x : GeneralLinear n E => x))) (e γ)
    let : LocallyCompactSpace (sigmaCentralizer σ n (e γ)) := hclosed.locallyCompactSpace
    let : SecondCountableTopology (sigmaCentralizer σ n (e γ)) :=
      Topology.IsEmbedding.subtypeVal.secondCountableTopology
    have hν : νδ = νγ.map (cosetHomeomorph e hH) := by
      simpa only [one_smul] using hνδ.eq_smul_of_subgroup_smul hclosed hν' (c := 1) (one_smul ..).symm
    rw [hν]
    exact twistedOrbitalIntegral_map_equiv e (MonoidHom.id _) (entrywiseAut σ n) hθ γ νγ φ

end DegreeOne

section Dual

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H] {V : Type uV} [AddCommGroup V] [Module ℂ V]

def smoothContragredientCompEquiv
    (ρ : Representation ℂ H V) (e : G ≃ₜ* H) :
    (smoothContragredient (ρ.comp e.toMonoidHom)).Equiv ((smoothContragredient ρ).comp e.toMonoidHom) := by
  have hs : smoothVectors (Representation.dual (ρ.comp e.toMonoidHom)) = smoothVectors ρ.dual :=
    Submodule.ext (isSmoothVector_dual_comp_continuousMulEquiv_iff ρ e)
  refine Representation.Equiv.mk (LinearEquiv.ofEq _ _ hs) fun g => ?_
  ext ℓ v
  change (ℓ : Module.Dual ℂ V) (ρ (e g⁻¹) v) = (ℓ : Module.Dual ℂ V) (ρ ((e g)⁻¹) v)
  rw [map_inv]

end Dual

/-- In a degree-one cyclic extension the stated self-pair polynomial identity
holds for all positive ranks and for the actual two irreducible actions. -/
def DegreeOneSigmaSelfPairEulerStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier],
    letI := F.canonicalTopologicalData.topology
    letI := E.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := E.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := E.canonicalTopologicalData.localField
    ∀ [IsModuleTopology F.Carrier E.Carrier] (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) (f r : ℕ),
      IsCyclicAlgebra σ 1 → IsResidueDegree F.Carrier E.Carrier f →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V] (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) (hπ : IsAdmissible π)
      (P : Representation ℂ (GeneralLinear (r + 1) E.Carrier) W) (hP : IsAdmissible P)
      (A : SigmaIntertwiner σ (r + 1) P) (c : ℂ), π.IsIrreducible → P.IsIrreducible →
      (letI := LocalFieldTopology.generalLinear_t2Space F.Carrier (r + 1)
       letI := LocalFieldTopology.generalLinear_locallyCompactSpace F.Carrier (r + 1)
       letI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F.Carrier (r + 1)
       letI := LocalFieldTopology.generalLinear_t2Space E.Carrier (r + 1)
       letI := LocalFieldTopology.generalLinear_locallyCompactSpace E.Carrier (r + 1)
       letI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E.Carrier (r + 1)
       IsSigmaLift σ 1 π hπ P hP A c) →
    ∀ (ψF : UnitaryAdditiveCharacter F.Carrier) (νF : SelfDualHaar F.canonicalTopologicalData ψF)
      (ψE : UnitaryAdditiveCharacter E.Carrier) (νE : SelfDualHaar E.canonicalTopologicalData ψE)
      (X : Finset (F.Carrierˣ →* ℂˣ)), (∀ κ, κ ∈ X ↔ IsNormTrivial E.Carrier κ) →
    ∀ (Q_E : Polynomial ℂ) (Q_F : X → Polynomial ℂ),
      IsPadicRankLPolynomial E ψE νE.val P (smoothContragredient P) Q_E →
      (∀ κ : X, IsPadicRankLPolynomial F ψF νF.val π
        (twist (κ.val.comp GeneralLinear.determinant) (smoothContragredient π)) (Q_F κ)) →
      Q_E.comp (Polynomial.X ^ f) = ∏ κ : X, Q_F κ

set_option maxHeartbeats 1700000 in
/-- The degree-one lift gives proportional characters after scalar transport.
Use separation of twisted distributions and invariance of the JPSS polynomial. -/
theorem degreeOneSigmaSelfPairEuler : DegreeOneSigmaSelfPairEulerStatement.{u,v,uV,uW} := by
  classical
  intro p _ F E _ _
  let TF := F.canonicalTopologicalData
  let TE := E.canonicalTopologicalData
  let := TF.topology
  let := TE.topology
  let := TF.valuativeRel
  let := TE.valuativeRel
  let := TF.localField
  let := TE.localField
  intro _ σ f r hcyc hf V _ _ W _ _ π hπ P hP A c hiπ hiP hlift ψF νF ψE νE X hX QE QF hQE hQF
  let n := r + 1
  let : Module.Finite F.Carrier E.Carrier := hcyc.1
  let := LocalFieldTopology.generalLinear_t2Space F.Carrier n
  let := LocalFieldTopology.generalLinear_locallyCompactSpace F.Carrier n
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F.Carrier n
  let := LocalFieldTopology.generalLinear_t2Space E.Carrier n
  let := LocalFieldTopology.generalLinear_locallyCompactSpace E.Carrier n
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E.Carrier n
  let : SecondCountableTopology (GeneralLinear n E.Carrier) :=
    LocalFieldTopology.generalLinear_secondCountableTopology E.Carrier n
  let := borel (GeneralLinear n F.Carrier)
  let : BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩
  let := borel (GeneralLinear n E.Carrier)
  let : BorelSpace (GeneralLinear n E.Carrier) := ⟨rfl⟩
  have hσ : σ = 1 := by simpa only [pow_one] using hcyc.pow_eq_one
  let a : F.Carrier ≃ₐ[F.Carrier] E.Carrier :=
    AlgEquiv.ofBijective (Algebra.ofId F.Carrier E.Carrier)
      ⟨(algebraMap F.Carrier E.Carrier).injective, fun x => hcyc.2.2.2.2 x (by rw [hσ]; rfl)⟩
  have ha : Continuous a := IsModuleTopology.continuous_of_linearMap a.toLinearMap
  have ha' : Continuous a.symm := IsModuleTopology.continuous_of_linearMap a.symm.toLinearMap
  let e := fieldEquiv n a.toRingEquiv ha ha'
  have he (g : GeneralLinear n F.Carrier) : e g = baseChange F.Carrier E.Carrier n g := rfl
  let μE : Measure (GeneralLinear n E.Carrier) := Measure.haar
  let μF := μE.map e.symm
  let : μF.IsHaarMeasure := e.symm.isHaarMeasure_map μE
  have hμ : μF.map e = μE := MeasurableEquiv.map_symm_map e.symm.toHomeomorph.toMeasurableEquiv
  let q : Representation ℂ (GeneralLinear n E.Carrier) V := π.comp e.symm.toMonoidHom
  have hq : IsAdmissible q := isAdmissible_comp_continuousMulEquiv π e.symm hπ
  have hiq : q.IsIrreducible :=
    CuspidalSupport.isIrreducible_comp_of_surjective π (hρ := hiπ) e.symm.toMonoidHom e.symm.surjective
  let B : SigmaIntertwiner σ n q := Representation.Equiv.mk (LinearEquiv.refl ℂ V) (fun g => by
    simp only [LinearEquiv.refl_toLinearMap, LinearMap.id_comp, LinearMap.comp_id]
    change q g = q (entrywiseAut σ n g)
    rw [hσ, entrywiseAut_one_apply])
  obtain ⟨j⟩ := nonempty_equiv_of_sigmaTwistedDistributions_proportional hcyc μE hP hq hiP hiq A B c
    (fun φ => by
      let φF := Hecke.TestFunction.pullback e.toHomeomorph φ
      have hm : AreConcordant σ 1 μF μE φ φF := hμ ▸ degreeOne_concordance hcyc e he μF ⇑φ
      have h := hlift.2 μF μE φ φF hm
      have hqφ := distribution_comp_equiv e.symm μE π hπ hq φ
      change twistedDistribution μE P hP A.toLinearMap φ =
        c * twistedDistribution μE q hq 1 φ
      rw [twistedDistribution_one, hqφ]
      exact h)
  have hcomp : q.comp e.toMonoidHom = π := by
    ext g x
    change π (e.symm (e g)) x = π g x
    rw [e.symm_apply_apply]
  let jF : Representation.Equiv (P.comp e.toMonoidHom) π :=
    hcomp ▸ Langlands.Representation.Equiv.compHom e.toMonoidHom j
  let jD := (smoothContragredientCompEquiv P e).symm.trans (smoothContragredientEquiv jF.symm)
  have hqFE := (LocalFieldData.ofInstances F.Carrier).residueCardinality_of_continuous_ringEquiv
    (LocalFieldData.ofInstances E.Carrier) a.toRingEquiv ha ha'
  have hf' : f = 1 := hf.unique (by
    unfold IsResidueDegree
    rw [pow_one]
    exact hqFE)
  have hnorm (x : F.Carrierˣ) : normUnits F.Carrier E.Carrier (Units.map (algebraMap F.Carrier E.Carrier) x) = x := by
    apply Units.ext
    change Algebra.norm F.Carrier (algebraMap F.Carrier E.Carrier (x : F.Carrier)) = (x : F.Carrier)
    rw [Algebra.norm_algebraMap, hcyc.2.1, pow_one]
  have htriv (κ : X) : κ.val = 1 := by
    apply MonoidHom.ext
    intro x
    rw [← hnorm x]
    exact ((hX κ.val).mp κ.property) (Units.map (algebraMap F.Carrier E.Carrier) x)
  let κ₀ : X := ⟨1, (hX 1).mpr fun _ => rfl⟩
  have hQ₀ := hQF κ₀
  change IsPadicRankLPolynomial F ψF νF.val π (twist ((1 : F.Carrierˣ →* ℂˣ).comp determinant)
    (smoothContragredient π)) (QF κ₀) at hQ₀
  have h1 : (1 : F.Carrierˣ →* ℂˣ).comp (determinant (n := n)) = 1 := rfl
  rw [h1, twist_one] at hQ₀
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel E.Carrier
  let : BorelSpace E.Carrier := ⟨rfl⟩
  let ψ := HarmonicAnalysis.FieldTransport.additiveCharacter a.toRingEquiv.symm ha ψE
  let ν := completionHaarPullback E a.toRingEquiv ha ha' νE.val
  have hψ (x : F.Carrier) : ψE (a x) = ψ x := rfl
  have hν : νE.val.measure = ν.measure.map a :=
    (congrArg AdditiveHaarMeasure.measure
      (HarmonicAnalysis.FieldTransport.haarMeasure_symm a.toRingEquiv.symm ha' ha νE.val)).symm
  have hpe := (isPadicSymmetricLPolynomial_of_le (Nat.le_refl r)).mp (isPadicRankLPolynomial_succ.mp hQE)
  have hpel := (RankinSelberg.FieldTransport.isLocalPairLPolynomial_comp_iff a.toRingEquiv ha ha' hψ hν
    P (smoothContragredient P) QE).mp hpe
  have hpel' := (IsPadicPairLPolynomial.congr_equiv jF jD).mp hpel
  obtain ⟨x, hx⟩ := TF.exists_unit_scale_eq ψF ψ
  have hpf := (RankinSelberg.Padic.isPadicPairLPolynomial_characterChange F ψF x νF.val π
    (smoothContragredient π) (QF κ₀)).mp
    ((isPadicSymmetricLPolynomial_of_le (Nat.le_refl r)).mp (isPadicRankLPolynomial_succ.mp hQ₀))
  rw [hx] at hpf
  rw [hf', pow_one, Polynomial.comp_X]
  exact (hpel'.unique_of_measure hpf).trans
    (Fintype.prod_eq_single κ₀ fun κ hne => (hne (Subtype.ext (htriv κ))).elim).symm

end Langlands.BaseChange
