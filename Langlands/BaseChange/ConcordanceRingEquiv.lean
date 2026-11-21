import Langlands.BaseChange.TwistedOrbitalEquiv

/-! # Change of coefficients for orbital concordance -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Langlands.JacquetLanglands Langlands.QuotientIntegration Langlands.TraceFormula

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v u' v'

section MatrixEquiv

variable {R : Type u} {S : Type u'} [CommRing R] [CommRing S]
  [TopologicalSpace R] [TopologicalSpace S] {n : ℕ}

/-- The entrywise topological group isomorphism of the actual matrix units. -/
def generalLinearRingEquiv (e : R ≃+* S) (he : Continuous e) (he' : Continuous e.symm) :
    GeneralLinear n R ≃ₜ* GeneralLinear n S where
  toMulEquiv := Units.mapEquiv e.mapMatrix.toMulEquiv
  continuous_toFun := Continuous.generalLinearGroup_map (f := e.toRingHom) he
  continuous_invFun := Continuous.generalLinearGroup_map (f := e.symm.toRingHom) he'

@[simp] theorem generalLinearRingEquiv_apply_apply
    (e : R ≃+* S) (he : Continuous e) (he' : Continuous e.symm)
    (g : GeneralLinear n R) (i j : Fin n) :
    generalLinearRingEquiv e he he' g i j = e (g i j) := rfl

end MatrixEquiv

section Algebra

variable {F : Type u} {E : Type v} {F' : Type u'} {E' : Type v'}
  [Field F] [CommRing E] [Algebra F E] [Field F'] [CommRing E'] [Algebra F' E']
  [TopologicalSpace F] [TopologicalSpace E] [TopologicalSpace F'] [TopologicalSpace E']
  {n l : ℕ} {σ : E ≃ₐ[F] E} {σ' : E' ≃ₐ[F'] E'}
variable (eF : F ≃+* F') (eE : E ≃+* E')
  (heF : Continuous eF) (heF' : Continuous eF.symm)
  (heE : Continuous eE) (heE' : Continuous eE.symm)
  (hι : ∀ a : F, eE (algebraMap F E a) = algebraMap F' E' (eF a))
  (hσ : ∀ a : E, eE (σ a) = σ' (eE a))

local notation "κF" => generalLinearRingEquiv (n := n) eF heF heF'
local notation "κE" => generalLinearRingEquiv (n := n) eE heE heE'

include hι in
theorem generalLinearRingEquiv_baseChange (γ : GeneralLinear n F) :
    κE (baseChange F E n γ) = baseChange F' E' n (κF γ) := by
  ext i j
  simp only [generalLinearRingEquiv_apply_apply, baseChange_apply_apply, hι]

include hσ in
omit [TopologicalSpace F] [TopologicalSpace F'] in
theorem generalLinearRingEquiv_entrywiseAut (δ : GeneralLinear n E) :
    κE (entrywiseAut σ n δ) = entrywiseAut σ' n (κE δ) := by
  ext i j
  simp only [generalLinearRingEquiv_apply_apply, entrywiseAut_apply_apply, hσ]

include hσ in
omit [TopologicalSpace F] [TopologicalSpace F'] in
theorem generalLinearRingEquiv_cyclicNorm (δ : GeneralLinear n E) :
    κE (cyclicNorm σ l δ) = cyclicNorm σ' l (κE δ) := by
  have hpow (k : ℕ) (d : GeneralLinear n E) :
      κE (entrywiseAut (σ ^ k) n d) = entrywiseAut (σ' ^ k) n (κE d) := by
    induction k generalizing d with
    | zero => simp only [pow_zero, entrywiseAut_one_apply]
    | succ k ih =>
      simp only [pow_succ, entrywiseAut_mul_apply, ih,
        generalLinearRingEquiv_entrywiseAut eE heE heE' hσ]
  induction l with
  | zero => simp only [cyclicNorm_zero, map_one]
  | succ l ih => rw [cyclicNorm_succ, cyclicNorm_succ, map_mul, ih, hpow]

include hι hσ in
theorem generalLinearRingEquiv_isNormAssociated_iff (δ : GeneralLinear n E)
    (γ : GeneralLinear n F) :
    IsNormAssociated σ' l (κE δ) (κF γ) ↔ IsNormAssociated σ l δ γ := by
  have hcomm (x : GeneralLinear n E) :
      κE (x⁻¹ * cyclicNorm σ l δ * x) =
        (κE x)⁻¹ * cyclicNorm σ' l (κE δ) * κE x := by
    rw [map_mul, map_mul, map_inv, generalLinearRingEquiv_cyclicNorm eE heE heE' hσ]
  have hbase := generalLinearRingEquiv_baseChange eF eE heF heF' heE heE' hι γ
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(κE).symm x, (κE).injective ?_⟩
    rw [hcomm, hbase, ContinuousMulEquiv.apply_symm_apply, hx]
  · rintro ⟨x, hx⟩
    refine ⟨κE x, ?_⟩
    rw [← hcomm, hx, hbase]

include heE heE' hι hσ in
theorem generalLinearRingEquiv_isNorm_iff (γ : GeneralLinear n F) :
    IsNorm σ' l (κF γ) ↔ IsNorm σ l γ := by
  constructor
  · rintro ⟨δ, hδ⟩
    obtain ⟨d, rfl⟩ := (κE).surjective δ
    exact ⟨d, (generalLinearRingEquiv_isNormAssociated_iff eF eE heF heF' heE heE'
      hι hσ d γ).1 hδ⟩
  · rintro ⟨δ, hδ⟩
    exact ⟨κE δ, (generalLinearRingEquiv_isNormAssociated_iff eF eE heF heF' heE heE'
      hι hσ δ γ).2 hδ⟩

private theorem generalLinearRingEquiv_charpoly (γ : GeneralLinear n F) :
    (κF γ : Matrix (Fin n) (Fin n) F').charpoly =
      (γ : Matrix (Fin n) (Fin n) F).charpoly.map eF.toRingHom := by
  change ((γ : Matrix (Fin n) (Fin n) F).map eF.toRingHom).charpoly = _
  rw [Matrix.charpoly_map]

theorem generalLinearRingEquiv_isRegularSemisimple_iff (γ : GeneralLinear n F) :
    IsRegularSemisimple (κF γ) ↔ IsRegularSemisimple γ := by
  unfold IsRegularSemisimple
  rw [generalLinearRingEquiv_charpoly eF heF heF']
  exact Polynomial.separable_map eF.toRingHom

theorem generalLinearRingEquiv_isRegularElliptic_iff (γ : GeneralLinear n F) :
    IsRegularElliptic (κF γ) ↔ IsRegularElliptic γ := by
  unfold IsRegularElliptic
  rw [generalLinearRingEquiv_isRegularSemisimple_iff eF heF heF',
    generalLinearRingEquiv_charpoly eF heF heF']
  exact and_congr_right fun _ => MulEquiv.irreducible_iff (Polynomial.mapEquiv eF)

variable [IsTopologicalRing F] [IsTopologicalRing E]
  [IsTopologicalRing F'] [IsTopologicalRing E']
  [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
  [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  [MeasurableSpace (GeneralLinear n F')] [BorelSpace (GeneralLinear n F')]
  [MeasurableSpace (GeneralLinear n E')] [BorelSpace (GeneralLinear n E')]
  (hF : Continuous (algebraMap F E)) (hF' : Continuous (algebraMap F' E'))

local notation "θ" => MulEquiv.toMonoidHom (entrywiseAut σ n)
local notation "θ'" => MulEquiv.toMonoidHom (entrywiseAut σ' n)
local notation "idF" => MonoidHom.id (GeneralLinear n F)
local notation "idF'" => MonoidHom.id (GeneralLinear n F')
local notation "hκE" => generalLinearRingEquiv_entrywiseAut eE heE heE' hσ
local notation "hκF" => (fun _ : GeneralLinear n F => rfl)

include hι hσ hF hF' in
omit [IsTopologicalRing F] [IsTopologicalRing F'] in
/-- Associated centralizer measures push forward to associated measures. -/
theorem isAssociatedMeasure_map_ringEquiv (δ : GeneralLinear n E) (γ : GeneralLinear n F)
    (μδ : Measure (sigmaCentralizer σ n δ)) (μγ : Measure (glCentralizer γ))
    (h : IsAssociatedMeasure σ l δ γ μδ μγ) :
    IsAssociatedMeasure σ' l (κE δ) (κF γ)
      (Measure.map (twistedCentralizerEquiv κE θ θ' hκE δ) μδ)
      (Measure.map (twistedCentralizerEquiv κF idF idF' hκF γ) μγ) := by
  obtain ⟨x, hx, hm⟩ := h
  refine ⟨κE x, ?_, ?_⟩
  · simpa only [map_inv, map_mul, generalLinearRingEquiv_cyclicNorm eE heE heE' hσ,
      generalLinearRingEquiv_baseChange eF eE heF heF' heE heE' hι] using congrArg κE hx
  · let eδ : sigmaCentralizer σ n δ ≃ₜ* sigmaCentralizer σ' n (κE δ) :=
      twistedCentralizerEquiv κE θ θ' hκE δ
    let eγ := twistedCentralizerEquiv κF idF idF' hκF γ
    have hconj : Measurable (fun c : sigmaCentralizer σ n δ => x⁻¹ * c.val * x) := by fun_prop
    have hconj' :
        Measurable (fun c : sigmaCentralizer σ' n (κE δ) => (κE x)⁻¹ * c.val * κE x) := by
      fun_prop
    have hbase : Measurable (fun t : glCentralizer γ => baseChange F E n t.val) :=
      ((hF.generalLinearGroup_map (n := Fin n)).comp continuous_subtype_val).measurable
    have hbase' : Measurable (fun t : glCentralizer (κF γ) => baseChange F' E' n t.val) :=
      ((hF'.generalLinearGroup_map (n := Fin n)).comp continuous_subtype_val).measurable
    have he : Measurable (κE : GeneralLinear n E → GeneralLinear n E') :=
      (κE).continuous.measurable
    have heδ : Measurable (eδ : sigmaCentralizer σ n δ → sigmaCentralizer σ' n (κE δ)) :=
      eδ.continuous.measurable
    have heδcoe (c : sigmaCentralizer σ n δ) : (eδ c : GeneralLinear n E') = κE c.val := rfl
    have heγ : Measurable (eγ : glCentralizer γ → glCentralizer (κF γ)) :=
      eγ.continuous.measurable
    have hmap := congrArg (Measure.map κE) hm
    rw [Measure.map_map he hconj, Measure.map_map he hbase] at hmap
    change Measure.map (fun c : sigmaCentralizer σ' n (κE δ) => (κE x)⁻¹ * c.val * κE x)
        (Measure.map eδ μδ) =
      Measure.map (fun t : glCentralizer (κF γ) => baseChange F' E' n t.val) (Measure.map eγ μγ)
    rw [Measure.map_map hconj' heδ, Measure.map_map hbase' heγ]
    simpa only [Function.comp_def, heδcoe, eγ, twistedCentralizerEquiv_apply_coe,
      map_mul, map_inv, generalLinearRingEquiv_baseChange eF eE heF heF' heE heE' hι] using hmap

variable (μF : Measure (GeneralLinear n F)) (μE : Measure (GeneralLinear n E))
  (φ : GeneralLinear n E' → ℂ) (f : GeneralLinear n F' → ℂ)

include hι hσ hF hF' in
/-- Pointwise orbital concordance for the image pair pulls back to the original pair. -/
theorem concordAt_pullback_ringEquiv (δ : GeneralLinear n E) (γ : GeneralLinear n F)
    (h : ConcordAt σ' l (Measure.map κF μF) (Measure.map κE μE) φ f (κE δ) (κF γ)) :
    ConcordAt σ l μF μE (φ ∘ κE) (f ∘ κF) δ γ := by
  intro μδ _ _ μγ _ _ νδ νγ hνδ hνγ hμ
  let eδ : sigmaCentralizer σ n δ ≃ₜ* sigmaCentralizer σ' n (κE δ) :=
    twistedCentralizerEquiv κE θ θ' hκE δ
  let eγ := twistedCentralizerEquiv κF idF idF' hκF γ
  let μδ' := Measure.map eδ μδ
  let μγ' := Measure.map eγ μγ
  let : μδ'.IsHaarMeasure := eδ.isHaarMeasure_map μδ
  let : μγ'.IsHaarMeasure := eγ.isHaarMeasure_map μγ
  let : μδ'.IsMulRightInvariant := isMulRightInvariant_map eδ μδ
  let : μγ'.IsMulRightInvariant := isMulRightInvariant_map eγ μγ
  let νδ' := Measure.map (twistedOrbitQuotientEquiv κE θ θ' hκE δ) νδ
  let νγ' := Measure.map (twistedOrbitQuotientEquiv κF idF idF' hκF γ) νγ
  let ηδ : Measure (twistedCentralizer θ δ) := μδ
  let : ηδ.IsMulRightInvariant := inferInstanceAs μδ.IsMulRightInvariant
  have h' := h μδ' μγ' νδ' νγ'
    (isCompatible_map_twistedOrbit κE θ θ' hκE δ μE ηδ νδ hνδ)
    (isCompatible_map_twistedOrbit κF idF idF' hκF γ μF μγ νγ hνγ)
    (isAssociatedMeasure_map_ringEquiv eF eE heF heF' heE heE' hι hσ hF hF'
      δ γ μδ μγ hμ)
  exact ((integrable_and_twistedOrbitalIntegral_map_equiv κE θ θ' hκE δ νδ φ).2.symm.trans h').trans
    (integrable_and_twistedOrbitalIntegral_map_equiv κF idF idF' hκF γ νγ f).2

include hι hσ hF hF' in
/-- Pullback preserves concordance on all regular pairs and off the norm image. -/
theorem areConcordant_pullback_ringEquiv
    (h : AreConcordant σ' l (Measure.map κF μF) (Measure.map κE μE) φ f) :
    AreConcordant σ l μF μE (φ ∘ κE) (f ∘ κF) := by
  constructor
  · intro γ hreg hnot μγ _ _ νγ hνγ
    let eγ := twistedCentralizerEquiv κF idF idF' hκF γ
    let μγ' := Measure.map eγ μγ
    let : μγ'.IsHaarMeasure := eγ.isHaarMeasure_map μγ
    let : μγ'.IsMulRightInvariant := isMulRightInvariant_map eγ μγ
    let νγ' := Measure.map (twistedOrbitQuotientEquiv κF idF idF' hκF γ) νγ
    exact (integrable_and_twistedOrbitalIntegral_map_equiv κF idF idF' hκF γ νγ f).2.symm.trans
      (h.1 (κF γ) ((generalLinearRingEquiv_isRegularSemisimple_iff eF heF heF' γ).2 hreg)
        (fun hn => hnot ((generalLinearRingEquiv_isNorm_iff eF eE heF heF' heE heE' hι hσ γ).1 hn))
        μγ' νγ' (isCompatible_map_twistedOrbit κF idF idF' hκF γ μF μγ νγ hνγ))
  · intro δ γ hδ hγ
    exact concordAt_pullback_ringEquiv eF eE heF heF' heE heE' hι hσ hF hF' μF μE φ f δ γ
      (h.2 _ _ ((generalLinearRingEquiv_isNormAssociated_iff eF eE heF heF' heE heE' hι hσ
        δ γ).2 hδ) ((generalLinearRingEquiv_isRegularSemisimple_iff eF heF heF' γ).2 hγ))

end Algebra

/-- Concordance pulls back along homeomorphic changes of coefficients that
commute with scalar extension and the twists. -/
def ConcordanceRingEquivStatement : Prop :=
  ∀ {F : Type u} {E : Type v} {F' : Type u'} {E' : Type v'}
    [Field F] [CommRing E] [Algebra F E] [Field F'] [CommRing E'] [Algebra F' E']
    [TopologicalSpace F] [TopologicalSpace E] [TopologicalSpace F'] [TopologicalSpace E']
    [IsTopologicalRing F] [IsTopologicalRing E] [IsTopologicalRing F'] [IsTopologicalRing E']
    {n l : ℕ} (σ : E ≃ₐ[F] E) (σ' : E' ≃ₐ[F'] E')
    [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
    [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
    [MeasurableSpace (GeneralLinear n F')] [BorelSpace (GeneralLinear n F')]
    [MeasurableSpace (GeneralLinear n E')] [BorelSpace (GeneralLinear n E')]
    (eF : F ≃+* F') (eE : E ≃+* E')
    (heF : Continuous eF) (heF' : Continuous eF.symm)
    (heE : Continuous eE) (heE' : Continuous eE.symm),
    (∀ a : F, eE (algebraMap F E a) = algebraMap F' E' (eF a)) →
    (∀ a : E, eE (σ a) = σ' (eE a)) →
    Continuous (algebraMap F E) → Continuous (algebraMap F' E') →
    ∀ (μF : Measure (GeneralLinear n F)) (μE : Measure (GeneralLinear n E))
      (φ : GeneralLinear n E' → ℂ) (f : GeneralLinear n F' → ℂ),
      let κF := generalLinearRingEquiv (n := n) eF heF heF'
      let κE := generalLinearRingEquiv (n := n) eE heE heE'
      let μF' := Measure.map κF μF
      let μE' := Measure.map κE μE
      (∀ δ γ, ConcordAt σ' l μF' μE' φ f (κE δ) (κF γ) →
        ConcordAt σ l μF μE (φ ∘ κE) (f ∘ κF) δ γ) ∧
      (AreConcordant σ' l μF' μE' φ f →
        AreConcordant σ l μF μE (φ ∘ κE) (f ∘ κF))

theorem concordanceRingEquiv : ConcordanceRingEquivStatement.{u, v, u', v'} := by
  intro F E F' E' _ _ _ _ _ _ _ _ _ _ _ _ _ _ n l σ σ'
    _ _ _ _ _ _ _ _ eF eE heF heF' heE heE' hι hσ hF hF' μF μE φ f
  exact ⟨concordAt_pullback_ringEquiv eF eE heF heF' heE heE' hι hσ hF hF' μF μE φ f,
    areConcordant_pullback_ringEquiv eF eE heF heF' heE heE' hι hσ hF hF' μF μE φ f⟩

end Langlands.BaseChange
