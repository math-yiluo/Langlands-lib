import Langlands.BaseChange.ConcordanceConjugation
import Langlands.BaseChange.ExactNormAssociatedMeasure
import Langlands.BaseChange.NormTrivialCharacterGroup
import Langlands.BaseChange.TwistedCharacterSeparation
import Langlands.BaseChange.TwistedLocalGroupTransport
import Langlands.Group.GL.RankReindex
import Langlands.VirtualRepresentation.Supercuspidal.FieldTransport

/-! # Supercuspidal σ-lift structure in extension degree one -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear HarmonicAnalysis JacquetLanglands MeasureTheory MeasureTheory.Measure
open QuotientIntegration TraceFormula

universe u v uV uW

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

private theorem cyclicNorm_one {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
    {σ : E ≃ₐ[F] E} {n : ℕ} (δ : GeneralLinear n E) :
    cyclicNorm σ 1 δ = δ := by
  rw [show (1 : ℕ) = 0 + 1 by rfl, cyclicNorm_succ, cyclicNorm_zero, pow_zero,
    entrywiseAut_one_apply, one_mul]

section DegreeOne

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {n : ℕ}

private theorem degreeOne_areConcordant [IsModuleTopology F E]
    [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
    [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
    (hσ : IsCyclicAlgebra σ 1) (e : GeneralLinear n F ≃ₜ* GeneralLinear n E)
    (he : ∀ g, e g = baseChange F E n g)
    (μ : Measure (GeneralLinear n F)) [μ.IsHaarMeasure] (φ : GeneralLinear n E → ℂ) :
    AreConcordant σ 1 μ (μ.map e) φ (φ ∘ e) := by
  let : (μ.map e).IsHaarMeasure := e.isHaarMeasure_map μ
  have hgen : σ = 1 := by simpa only [pow_one] using hσ.pow_eq_one
  have hact (g : GeneralLinear n E) : entrywiseAut σ n g = g := by
    rw [hgen, entrywiseAut_one_apply]
  have hbase : Measurable (baseChange F E n) := by
    rw [← funext he]
    exact e.continuous.measurable
  constructor
  · intro γ _ hnon
    exfalso
    exact hnon ⟨baseChange F E n γ, 1, by
      rw [cyclicNorm_one, inv_one, one_mul, mul_one]⟩
  · intro δ γ _ hγ
    refine concordAt_of_conj_of_cyclicNorm_eq hσ.pow_eq_one hbase δ γ 1 ?_
    intro δ' hn
    simp only [inv_one, one_mul, mul_one] at hn ⊢
    have hδ' : e γ = δ' := by rw [he, ← hn, cyclicNorm_one]
    subst δ'
    let hC (g : GeneralLinear n F) : e g ∈ sigmaCentralizer σ n (e γ) ↔
        g ∈ glCentralizer γ :=
      map_mem_twistedCentralizer_iff e (MonoidHom.id _) (entrywiseAut σ n)
        (fun x => (hact (e x)).symm) γ g
    let C := subgroupEquiv e hC
    intro μδ _ _ μγ _ _ νδ νγ hνδ hνγ hμ
    have := LocalFieldTopology.generalLinear_t2Space E n
    have := LocalFieldTopology.generalLinear_locallyCompactSpace E n
    have := LocalFieldTopology.generalLinear_secondCountableTopology E n
    have : BorelSpace (sigmaCentralizer σ n (e γ)) := Subtype.borelSpace _
    have : BorelSpace (glCentralizer γ) := Subtype.borelSpace _
    have hCeq : exactNormCentralizerEquiv hσ hγ hn = C := by
      apply ContinuousMulEquiv.ext
      intro t
      apply Subtype.ext
      exact (exactNormCentralizerEquiv_apply_val hσ hγ hn t).trans (he t.val).symm
    have hμeq : μδ = μγ.map C :=
      ((isAssociatedMeasure_iff_map_exactNormCentralizerEquiv hσ hγ hn μδ μγ).mp hμ).trans
        (congrArg (fun k : glCentralizer γ ≃ₜ* sigmaCentralizer σ n (e γ) =>
          μγ.map k) hCeq)
    have hνmap := (isCompatible_map_iff e hC μ μγ (μ.map e) μδ rfl hμeq νγ).mpr hνγ
    have hθ : Continuous (fun g : GeneralLinear n E => entrywiseAut σ n g) := by
      simpa only [hact] using (continuous_id' : Continuous (fun g : GeneralLinear n E => g))
    have hc := isClosed_twistedCentralizer (entrywiseAut σ n) hθ (e γ)
    have := hc.locallyCompactSpace
    have : SecondCountableTopology (sigmaCentralizer σ n (e γ)) :=
      Topology.IsEmbedding.subtypeVal.secondCountableTopology
    have hνeq : νδ = νγ.map (cosetHomeomorph e hC) := by
      simpa only [one_smul] using
        hνδ.eq_smul_of_subgroup_smul hc hνmap (c := 1) (one_smul ..).symm
    rw [hνeq]
    exact twistedOrbitalIntegral_map_equiv e (MonoidHom.id _) (entrywiseAut σ n)
      (fun g => (hact (e g)).symm) γ νγ φ

private theorem isSupercuspidal_degreeOne_lift [IsModuleTopology F E]
    [T2Space (GeneralLinear n F)] [LocallyCompactSpace (GeneralLinear n F)]
    [TotallyDisconnectedSpace (GeneralLinear n F)]
    [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
    [TotallyDisconnectedSpace (GeneralLinear n E)]
    (hσ : IsCyclicAlgebra σ 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GeneralLinear n F) V} (hπ : IsAdmissible π)
    (hπi : π.IsIrreducible) (hπs : IsSupercuspidal π)
    {P : Representation ℂ (GeneralLinear n E) W} (hP : IsAdmissible P)
    (hPi : P.IsIrreducible) (A : SigmaIntertwiner σ n P) (c : ℂ)
    (hlift : IsSigmaLift σ 1 π hπ P hP A c) : IsSupercuspidal P := by
  have hgen : σ = 1 := by simpa only [pow_one] using hσ.pow_eq_one
  let a : F ≃ₐ[F] E := AlgEquiv.ofBijective (Algebra.ofId F E)
    ⟨(algebraMap F E).injective, fun x => hσ.2.2.2.2 x (by rw [hgen]; rfl)⟩
  have ha : Continuous a := IsModuleTopology.continuous_of_linearMap a.toLinearMap
  have ha' : Continuous a.symm := IsModuleTopology.continuous_of_linearMap a.symm.toLinearMap
  let e := fieldEquiv n a.toRingEquiv ha ha'
  have he (g : GeneralLinear n F) : e g = baseChange F E n g := by
    ext i j
    rfl
  let : MeasurableSpace (GeneralLinear n F) := borel _
  let : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear n E) := borel _
  let : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  let μ := haarMeasure (G := GeneralLinear n F) (Classical.arbitrary _)
  let : (μ.map e).IsHaarMeasure := e.isHaarMeasure_map μ
  let P₀ : Representation ℂ (GeneralLinear n F) W := P.comp e.toMonoidHom
  have hP₀ := isAdmissible_comp_continuousMulEquiv P e hP
  have hP₀i := (isIrreducible_comp_continuousMulEquiv_iff P e).mpr hPi
  let A₀ : P₀.Equiv (P₀.comp (1 : MulAut (GeneralLinear n F)).toMonoidHom) :=
    Representation.Equiv.mk A.toLinearEquiv (fun g => by
      change A.toLinearMap ∘ₗ P (e g) = P (e g) ∘ₗ A.toLinearMap
      simpa only [hgen, entrywiseAut_one_apply] using A.comp_apply_eq (e g))
  let B : π.Equiv (π.comp (1 : MulAut (GeneralLinear n F)).toMonoidHom) :=
    Representation.Equiv.mk (LinearEquiv.refl ℂ V) (fun _ => by simp)
  obtain ⟨b⟩ := twistedCharacterSeparation _ μ 1 continuous_id 1 Nat.one_pos (one_pow 1)
    W V P₀ π hP₀ hπ hP₀i hπi A₀ B c (fun f => by
      let φ := Hecke.TestFunction.pullback e.symm.toHomeomorph f
      have hφ : (φ : GeneralLinear n E → ℂ) ∘ e = f := by
        funext g
        exact congrArg f (e.symm_apply_apply g)
      have hmatch := degreeOne_areConcordant hσ e he μ φ
      rw [hφ] at hmatch
      have htrace := hlift.2 μ (μ.map e) φ f hmatch
      rw [← twistedDistribution_comp_equiv e μ P hP hP₀ A.toLinearMap f] at htrace
      change twistedDistribution μ (P.comp e.toMonoidHom) hP₀ A.toLinearMap f =
        c * twistedDistribution μ π hπ 1 f
      rwa [twistedDistribution_one])
  exact (isSupercuspidal_comp_fieldEquiv_iff n a.toRingEquiv ha ha' P).mp
    ((isSupercuspidal_iff_of_equiv b).mpr hπs)

end DegreeOne

/-- In extension degree one, the lift itself is a supercuspidal orbit block and the
norm-twist stabilizer has order one. -/
def CuspidalSigmaLiftStructureDegreeOneStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (n : ℕ), IsCyclicAlgebra σ 1 → ∀ hn : 0 < n,
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GeneralLinear n F) V) (hπ : IsAdmissible π),
      IsSupercuspidal π → π.IsIrreducible →
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (P : Representation ℂ (GeneralLinear n E) W) (hP : IsAdmissible P),
      P.IsIrreducible →
    ∀ (A : SigmaIntertwiner σ n P) (c : ℂ),
      (haveI := LocalFieldTopology.generalLinear_t2Space F n
       haveI := LocalFieldTopology.generalLinear_locallyCompactSpace F n
       haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
       haveI := LocalFieldTopology.generalLinear_t2Space E n
       haveI := LocalFieldTopology.generalLinear_locallyCompactSpace E n
       haveI := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E n
       IsSigmaLift σ 1 π hπ P hP A c) →
      Nat.card (normTwistStabilizer E π) = 1 ∧ IsSupercuspidal P ∧
      (∀ i : ℕ, Nonempty (P.Equiv (P.comp (entrywiseAut (σ ^ i) n).toMonoidHom))) ∧
      Nonempty (P.Equiv ((sigmaOrbitProduct σ 1 hn P).comp
        (GeneralLinear.reindex (R := E) (finCongr (Nat.one_mul n))).symm.toMonoidHom))

/-- Degree-one structure by change of variables in the distributional lift identity. -/
theorem cuspidalSigmaLiftStructure_degreeOne : CuspidalSigmaLiftStructureDegreeOneStatement := by
  intro F _ _ _ _ _ E _ _ _ _ _ _ σ n hσ hn V _ _ π hπ hπs hπi W _ _ P hP hPi A c hlift
  have := LocalFieldTopology.generalLinear_t2Space F n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  have := LocalFieldTopology.generalLinear_t2Space E n
  have := LocalFieldTopology.generalLinear_locallyCompactSpace E n
  have := LocalFieldTopology.generalLinear_totallyDisconnectedSpace E n
  have hgen : σ = 1 := by simpa only [pow_one] using hσ.pow_eq_one
  refine ⟨Nat.dvd_one.mp (normTwistStabilizer_card_dvd hσ π),
    isSupercuspidal_degreeOne_lift hσ hπ hπi hπs hP hPi A c hlift, ?_, ?_⟩
  · intro i
    exact ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ W) (fun g => by
      simp only [LinearEquiv.refl_toLinearMap, LinearMap.id_comp, LinearMap.comp_id,
        MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hgen, one_pow, entrywiseAut_one_apply])⟩
  · obtain ⟨b⟩ := sigmaOrbitProduct_one_equiv σ hn P hP.1
    let r := GeneralLinear.reindex (R := E) (finCongr (Nat.one_mul n))
    have hr : (GeneralLinear.reindex (R := E) (finCongr (Nat.one_mul n).symm)).symm = r := by
      apply MulEquiv.ext
      intro g
      apply Units.ext
      apply Matrix.ext
      intro i j
      rw [reindex_finCongr_symm_apply, reindex_finCongr_apply]
    rw [hr] at b
    have hcomp : (P.comp r.toMonoidHom).comp r.symm.toMonoidHom = P := by
      ext g : 1
      exact congrArg P (r.apply_symm_apply g)
    have b' := CuspidalSupport.equivComp b.symm r.symm.toMonoidHom
    rw [hcomp] at b'
    exact ⟨b'⟩

end Langlands.BaseChange
