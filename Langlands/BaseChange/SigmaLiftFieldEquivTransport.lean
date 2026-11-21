import Langlands.BaseChange.TwistedCharacter
import Langlands.BaseChange.TwistedLocalGroupTransport
import Langlands.VirtualRepresentation.Supercuspidal.FieldTransport

/-! # Transport of matching local test functions and sigma-lifts through field isomorphisms -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v u' v'

namespace Langlands.BaseChange

open GeneralLinear MeasureTheory MeasureTheory.Measure QuotientIntegration TraceFormula JacquetLanglands

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

section Transport

variable {F : Type u} {E : Type v} {F' : Type u'} {E' : Type v'}
  [Field F] [Field E] [Field F'] [Field E'] [Algebra F E] [Algebra F' E']
  [TopologicalSpace F] [TopologicalSpace E] [TopologicalSpace F'] [TopologicalSpace E']
  {n : ℕ}
  (a : F ≃+* F') (b : E ≃+* E') (ha : Continuous a) (ha' : Continuous a.symm)
  (hb : Continuous b) (hb' : Continuous b.symm)
  (hab : ∀ x, b (algebraMap F E x) = algebraMap F' E' (a x))
  (σ : E ≃ₐ[F] E) (τ : E' ≃ₐ[F'] E') (hστ : ∀ x, b (σ x) = τ (b x))

local notation "eF" => fieldEquiv n a ha ha'
local notation "eE" => fieldEquiv n b hb hb'
local notation "θ" => MulEquiv.toMonoidHom (entrywiseAut σ n)
local notation "θ'" => MulEquiv.toMonoidHom (entrywiseAut τ n)

omit [TopologicalSpace F] [TopologicalSpace F'] in
include hστ in
theorem fieldEquiv_entrywiseAut (g : GeneralLinear n E) : eE (θ g) = θ' (eE g) := by
  ext i j
  exact hστ (g i j)

include hab in
private theorem fieldEquiv_baseChange (g : GeneralLinear n F) :
    eE (baseChange F E n g) = baseChange F' E' n (eF g) := by
  ext i j
  exact hab (g i j)

omit [TopologicalSpace F] [TopologicalSpace F'] in
include hστ in
private theorem fieldEquiv_cyclicNorm (l : ℕ) (g : GeneralLinear n E) :
    eE (cyclicNorm σ l g) = cyclicNorm τ l (eE g) := by
  have hpow (i : ℕ) (x : E) : b ((σ ^ i) x) = (τ ^ i) (b x) := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ', pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, hστ, ih]
  induction l with
  | zero => simp
  | succ l ih =>
    rw [cyclicNorm_succ, cyclicNorm_succ, map_mul, ih]
    congr 1
    ext i j
    exact hpow l (g i j)

include hab hστ in
/-- Norm association is preserved and reflected by compatible field isomorphisms. -/
theorem fieldEquiv_isNormAssociated_iff (l : ℕ) (δ : GeneralLinear n E) (γ : GeneralLinear n F) :
    IsNormAssociated τ l (eE δ) (eF γ) ↔ IsNormAssociated σ l δ γ := by
  have hmap (x : GeneralLinear n E) :
      eE (x⁻¹ * cyclicNorm σ l δ * x) = (eE x)⁻¹ * cyclicNorm τ l (eE δ) * eE x := by
    simp only [map_mul, map_inv, fieldEquiv_cyclicNorm b hb hb' σ τ hστ l δ]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := (eE).surjective y
    exact ⟨x, (eE).injective ((hmap x).trans
      (hy.trans (fieldEquiv_baseChange a b ha ha' hb hb' hab γ).symm))⟩
  · rintro ⟨x, hx⟩
    exact ⟨eE x, (hmap x).symm.trans
      ((congrArg eE hx).trans (fieldEquiv_baseChange a b ha ha' hb hb' hab γ))⟩

private theorem isRegularSemisimple_fieldEquiv_iff (γ : GeneralLinear n F) :
    IsRegularSemisimple (eF γ) ↔ IsRegularSemisimple γ := by
  unfold IsRegularSemisimple
  change (γ.val.map a.toRingHom).charpoly.Separable ↔ γ.val.charpoly.Separable
  rw [Matrix.charpoly_map, _root_.Polynomial.separable_map]

variable [IsTopologicalRing F] [IsTopologicalRing E] [IsTopologicalRing F'] [IsTopologicalRing E']
  [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
  [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  [MeasurableSpace (GeneralLinear n F')] [BorelSpace (GeneralLinear n F')]
  [MeasurableSpace (GeneralLinear n E')] [BorelSpace (GeneralLinear n E')]

local notation "hOrd" => (fun _ => rfl)
local notation "hTw" => fieldEquiv_entrywiseAut b hb hb' σ τ hστ

include hab hστ in
omit [IsTopologicalRing F] [IsTopologicalRing F'] in
private theorem isAssociatedMeasure_map (l : ℕ) (δ : GeneralLinear n E) (γ : GeneralLinear n F)
    (hA : Continuous (algebraMap F E)) (hA' : Continuous (algebraMap F' E'))
    (μδ : Measure (sigmaCentralizer σ n δ)) (μγ : Measure (glCentralizer γ))
    (h : IsAssociatedMeasure σ l δ γ μδ μγ) :
    IsAssociatedMeasure τ l (eE δ) (eF γ)
      (μδ.map (subgroupEquiv eE (map_mem_twistedCentralizer_iff eE θ θ' hTw δ)))
      (μγ.map (subgroupEquiv eF (map_mem_twistedCentralizer_iff eF (MonoidHom.id _)
        (MonoidHom.id _) hOrd γ))) := by
  obtain ⟨x, hx, hμ⟩ := h
  refine ⟨eE x, ?_, ?_⟩
  · simpa only [map_mul, map_inv, fieldEquiv_cyclicNorm b hb hb' σ τ hστ l δ,
      fieldEquiv_baseChange a b ha ha' hb hb' hab γ] using congrArg eE hx
  · let H : sigmaCentralizer σ n δ ≃ₜ* sigmaCentralizer τ n (eE δ) :=
      subgroupEquiv eE (map_mem_twistedCentralizer_iff eE θ θ' hTw δ)
    let K := subgroupEquiv eF (map_mem_twistedCentralizer_iff eF
      (MonoidHom.id _) (MonoidHom.id _) hOrd γ)
    let f (z : sigmaCentralizer σ n δ) := x⁻¹ * (z : GeneralLinear n E) * x
    let g (z : glCentralizer γ) := baseChange F E n (z : GeneralLinear n F)
    let f' (z : sigmaCentralizer τ n (eE δ)) := (eE x)⁻¹ * (z : GeneralLinear n E') * eE x
    let g' (z : glCentralizer (eF γ)) := baseChange F' E' n (z : GeneralLinear n F')
    change Measure.map f' (Measure.map H μδ) = Measure.map g' (Measure.map K μγ)
    have hf : Continuous f := (continuous_const.mul continuous_subtype_val).mul continuous_const
    have hf' : Continuous f' := (continuous_const.mul continuous_subtype_val).mul continuous_const
    have hg : Continuous g := hA.generalLinearGroup_map.comp continuous_subtype_val
    have hg' : Continuous g' := hA'.generalLinearGroup_map.comp continuous_subtype_val
    have h1 : f' ∘ H = eE ∘ f := by
      funext z
      change (eE x)⁻¹ * eE (z : GeneralLinear n E) * eE x =
        eE (x⁻¹ * (z : GeneralLinear n E) * x)
      simp only [map_mul, map_inv]
    have h2 : g' ∘ K = eE ∘ g := by
      funext z
      exact (fieldEquiv_baseChange a b ha ha' hb hb' hab z.val).symm
    have hH : Measurable (H : _ → _) := H.continuous.measurable
    have hK : Measurable (K : _ → _) := K.continuous.measurable
    have he : Measurable (eE : _ → _) := (eE).continuous.measurable
    rw [Measure.map_map hf'.measurable hH, h1, Measure.map_map hg'.measurable hK, h2,
      ← Measure.map_map he hf.measurable, ← Measure.map_map he hg.measurable]
    exact congrArg (Measure.map eE) hμ

include hab hστ in
/-- Pullback of matching tests along the actual pair of compatible field
isomorphisms preserves concordance. The target ambient measures are the
pushforwards of the source ambient measures. -/
theorem areConcordant_pullback_fieldEquiv (l : ℕ)
    (hA : Continuous (algebraMap F E)) (hA' : Continuous (algebraMap F' E'))
    (μF : Measure (GeneralLinear n F)) (μE : Measure (GeneralLinear n E))
    (φ : GeneralLinear n E' → ℂ) (f : GeneralLinear n F' → ℂ)
    (h : AreConcordant τ l (μF.map eF) (μE.map eE) φ f) :
    AreConcordant σ l μF μE (φ ∘ eE) (f ∘ eF) := by
  constructor
  · intro γ hγ hn μγ _ _ νγ hνγ
    have hn' : ¬ IsNorm τ l (eF γ) := by
      rintro ⟨δ', hδ'⟩
      obtain ⟨δ, rfl⟩ := (eE).surjective δ'
      exact hn ⟨δ, (fieldEquiv_isNormAssociated_iff a b ha ha' hb hb' hab σ τ hστ l δ γ).mp hδ'⟩
    let hK := map_mem_twistedCentralizer_iff eF (MonoidHom.id _) (MonoidHom.id _) hOrd γ
    let K := subgroupEquiv eF hK
    let := K.isHaarMeasure_map μγ
    let := isMulRightInvariant_map_mulEquiv μγ K.toMulEquiv K.continuous.measurable
    have hν' := (isCompatible_map_iff eF hK μF μγ _ _ rfl rfl νγ).mpr hνγ
    exact (twistedOrbitalIntegral_map_equiv eF (MonoidHom.id _) (MonoidHom.id _) hOrd γ νγ f).symm.trans
      (h.1 (eF γ) ((isRegularSemisimple_fieldEquiv_iff a ha ha' γ).mpr hγ) hn' (μγ.map K) _ hν')
  · intro δ γ hd hγ μδ _ _ μγ _ _ νδ νγ hνδ hνγ hμ
    let hH : ∀ x, eE x ∈ sigmaCentralizer τ n (eE δ) ↔ x ∈ sigmaCentralizer σ n δ :=
      map_mem_twistedCentralizer_iff eE θ θ' hTw δ
    let hK := map_mem_twistedCentralizer_iff eF (MonoidHom.id _) (MonoidHom.id _) hOrd γ
    let H : sigmaCentralizer σ n δ ≃ₜ* sigmaCentralizer τ n (eE δ) :=
      subgroupEquiv eE hH
    let K := subgroupEquiv eF hK
    let := H.isHaarMeasure_map μδ
    let := K.isHaarMeasure_map μγ
    let := isMulRightInvariant_map_mulEquiv μδ H.toMulEquiv H.continuous.measurable
    let := isMulRightInvariant_map_mulEquiv μγ K.toMulEquiv K.continuous.measurable
    have hνδ' := (isCompatible_map_iff eE hH μE μδ _ _ rfl rfl νδ).mpr hνδ
    have hνγ' := (isCompatible_map_iff eF hK μF μγ _ _ rfl rfl νγ).mpr hνγ
    have hμ' := isAssociatedMeasure_map a b ha ha' hb hb' hab σ τ hστ l δ γ hA hA' μδ μγ hμ
    have hd' := (fieldEquiv_isNormAssociated_iff a b ha ha' hb hb' hab σ τ hστ l δ γ).mpr hd
    have hγ' := (isRegularSemisimple_fieldEquiv_iff a ha ha' γ).mpr hγ
    have heq := h.2 (eE δ) (eF γ) hd' hγ' (μδ.map H) (μγ.map K) _ _ hνδ' hνγ' hμ'
    exact (twistedOrbitalIntegral_map_equiv eE θ θ' hTw δ νδ φ).symm.trans
      (heq.trans (twistedOrbitalIntegral_map_equiv eF (MonoidHom.id _) (MonoidHom.id _) hOrd γ νγ f))

end Transport


section SigmaLift

open HarmonicAnalysis

universe uV uW

/-- Compatible topological field isomorphisms pull back the distributional
sigma-lift identity with the same constant and the same intertwining operator. -/
def SigmaLiftFieldEquivTransportStatement : Prop :=
  ∀ (F : Type u) (E : Type v) (F' : Type u') (E' : Type v')
    [Field F] [Field E] [Field F'] [Field E'] [Algebra F E] [Algebra F' E']
    [TopologicalSpace F] [TopologicalSpace E] [TopologicalSpace F'] [TopologicalSpace E']
    [IsTopologicalRing F] [IsTopologicalRing E] [IsTopologicalRing F'] [IsTopologicalRing E']
    (n l : ℕ)
    [T2Space (GeneralLinear n F)] [LocallyCompactSpace (GeneralLinear n F)]
    [TotallyDisconnectedSpace (GeneralLinear n F)]
    [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
    [TotallyDisconnectedSpace (GeneralLinear n E)]
    [T2Space (GeneralLinear n F')] [LocallyCompactSpace (GeneralLinear n F')]
    [TotallyDisconnectedSpace (GeneralLinear n F')]
    [T2Space (GeneralLinear n E')] [LocallyCompactSpace (GeneralLinear n E')]
    [TotallyDisconnectedSpace (GeneralLinear n E')]
    (a : F ≃+* F') (b : E ≃+* E') (ha : Continuous a) (ha' : Continuous a.symm)
    (hb : Continuous b) (hb' : Continuous b.symm),
    Continuous (algebraMap F E) → Continuous (algebraMap F' E') →
    (∀ x, b (algebraMap F E x) = algebraMap F' E' (a x)) →
    ∀ (σ : E ≃ₐ[F] E) (τ : E' ≃ₐ[F'] E'), (∀ x, b (σ x) = τ (b x)) →
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (π' : Representation ℂ (GeneralLinear n F') V) (ρ' : Representation ℂ (GeneralLinear n E') W)
      (hπ' : IsAdmissible π') (hρ' : IsAdmissible ρ') (A' : SigmaIntertwiner τ n ρ') (c : ℂ),
      IsSigmaLift τ l π' hπ' ρ' hρ' A' c →
      let π := π'.comp (fieldEquiv n a ha ha').toMonoidHom
      let ρ := ρ'.comp (fieldEquiv n b hb hb').toMonoidHom
      ∃ (hπ : IsAdmissible π) (hρ : IsAdmissible ρ) (A : SigmaIntertwiner σ n ρ),
        A.toLinearMap = A'.toLinearMap ∧ IsSigmaLift σ l π hπ ρ hρ A c

set_option maxHeartbeats 1200000 in
/-- Map each concordant test pair and its Haar measures and compare the two
actual integrated characters. -/
theorem sigmaLiftFieldEquivTransport : SigmaLiftFieldEquivTransportStatement.{u, v, u', v', uV, uW} := by
  intro F E F' E' _ _ _ _ _ _ _ _ _ _ _ _ _ _ n l _ _ _ _ _ _ _ _ _ _ _ _
    a b ha ha' hb hb' hA hA' hab σ τ hστ V _ _ W _ _ π' ρ' hπ' hρ' A' c h π ρ
  let eF := fieldEquiv n a ha ha'
  let eE := fieldEquiv n b hb hb'
  have hπ : IsAdmissible π := isAdmissible_comp_continuousMulEquiv π' eF hπ'
  have hρ : IsAdmissible ρ := isAdmissible_comp_continuousMulEquiv ρ' eE hρ'
  let A : SigmaIntertwiner σ n ρ := Representation.Equiv.mk A'.toLinearEquiv (fun x => by
    change A'.toLinearMap ∘ₗ ρ' (eE x) =
      ρ' (eE (entrywiseAut σ n x)) ∘ₗ A'.toLinearMap
    have hcomm : eE (entrywiseAut σ n x) = entrywiseAut τ n (eE x) :=
      fieldEquiv_entrywiseAut b hb hb' σ τ hστ x
    rw [hcomm]
    exact A'.isIntertwining' (eE x))
  refine ⟨hπ, hρ, A, rfl, h.1, ?_⟩
  let : MeasurableSpace (GeneralLinear n F) := borel _
  let : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear n E) := borel _
  let : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear n F') := borel _
  let : BorelSpace (GeneralLinear n F') := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear n E') := borel _
  let : BorelSpace (GeneralLinear n E') := ⟨rfl⟩
  intro μF _ μE _ φ f hm
  let μF' := μF.map eF
  let μE' := μE.map eE
  let : μF'.IsHaarMeasure := eF.isHaarMeasure_map μF
  let : μE'.IsHaarMeasure := eE.isHaarMeasure_map μE
  let f' := Hecke.TestFunction.pullback eF.symm.toHomeomorph f
  let φ' := Hecke.TestFunction.pullback eE.symm.toHomeomorph φ
  have hab' (x : F') : b.symm (algebraMap F' E' x) = algebraMap F E (a.symm x) := by
    apply b.injective
    rw [b.apply_symm_apply, hab, a.apply_symm_apply]
  have hτσ (x : E') : b.symm (τ x) = σ (b.symm x) := by
    apply b.injective
    rw [b.apply_symm_apply, hστ, b.apply_symm_apply]
  have hFμ : μF'.map eF.symm = μF :=
    MeasurableEquiv.map_symm_map eF.toHomeomorph.toMeasurableEquiv
  have hEμ : μE'.map eE.symm = μE :=
    MeasurableEquiv.map_symm_map eE.toHomeomorph.toMeasurableEquiv
  have hm' : AreConcordant τ l μF' μE' φ' f' :=
    areConcordant_pullback_fieldEquiv a.symm b.symm ha' ha hb' hb hab' τ σ hτσ l hA' hA μF' μE' φ f
      (by change AreConcordant σ l (μF'.map eF.symm) (μE'.map eE.symm) φ f
          rwa [hFμ, hEμ])
  change twistedDistribution μE ρ hρ A'.toLinearMap φ = c * Character.distribution μF π hπ f
  exact (twistedDistribution_comp_equiv eE μE ρ' hρ' hρ A'.toLinearMap φ).trans
    ((h.2 μF' μE' φ' f' hm').trans (congrArg (c * ·) (distribution_comp_equiv eF μF π' hπ' hπ f).symm))

end SigmaLift

end Langlands.BaseChange
