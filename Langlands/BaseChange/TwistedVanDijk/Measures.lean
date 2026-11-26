import Langlands.BaseChange.TwistedVanDijk.Groups
import Langlands.Analysis.Local.CompactFactorizationHaar

/-! # Haar measures for the twisted van Dijk formula

Haar measures on `G = GL_n(E)`, on the Levi `M`, on the unipotent radical `U` and on
`K = GL_n(𝒪_E)` with Henniart–Lemaire's normalizations: their invariance under the entrywise
action of `σ`, the Iwasawa decomposition `dg = dm du dk`, and integrals over `K` of functions
invariant under an open subgroup. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedVanDijk

open MeasureTheory Measure GeneralLinear
open scoped ENNReal NNReal

universe u v

section Uniqueness

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

omit [LocallyCompactSpace G] in
/-- Two σ-finite left invariant measures giving mass one to the same compact set with nonempty
interior are equal. -/
theorem eq_of_isMulLeftInvariant_of_eq_one (μ ν : Measure G) [SigmaFinite μ]
    [μ.IsMulLeftInvariant] [SigmaFinite ν] [ν.IsMulLeftInvariant] {C : Set G}
    (hC : IsCompact C) (hC' : (interior C).Nonempty) (hμ : μ C = 1) (hν : ν C = 1) : μ = ν := by
  rw [← (haarMeasure_eq_iff ⟨⟨C, hC⟩, hC'⟩ μ).mpr hμ,
    ← (haarMeasure_eq_iff ⟨⟨C, hC⟩, hC'⟩ ν).mpr hν]

/-- A Haar measure is invariant under a topological group automorphism that preserves a compact
open set. -/
theorem map_eq_self_of_preimage_eq (μ : Measure G) [μ.IsHaarMeasure] (θ : G ≃ₜ* G)
    {C : Set G} (hC : IsCompact C) (hCo : IsOpen C) (hne : C.Nonempty) (hθ : θ ⁻¹' C = C) :
    μ.map θ = μ := by
  have : (μ.map θ).IsHaarMeasure := θ.isHaarMeasure_map μ
  have hc0 : μ C ≠ 0 := hCo.measure_ne_zero μ hne
  have hct : μ C ≠ ⊤ := hC.measure_lt_top.ne
  have hmap : (μ.map θ) C = μ C := by
    rw [Measure.map_apply (map_continuous θ).measurable hCo.measurableSet, hθ]
  have h := isMulLeftInvariant_eq_smul (μ.map θ) μ
  set s := haarScalarFactor (μ.map θ) μ
  have hs : (s : ℝ≥0∞) * μ C = 1 * μ C := by
    have h1 := congrArg (fun ν : Measure G => ν C) h
    simp only [Measure.smul_apply, nnreal_smul_coe_apply] at h1
    rw [one_mul, ← h1, hmap]
  have hs1 : s = 1 := by
    exact_mod_cast (ENNReal.mul_left_inj hc0 hct).mp hs
  rw [h, hs1, one_smul]

end Uniqueness

section CosetSum

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H]

/-- The integral of a function invariant under right translation by a subgroup `H'` of finite
index with measurable cosets is a finite sum over representatives of the left cosets. -/
theorem integral_eq_sum_quotient_out (μ : Measure H) [μ.IsMulLeftInvariant]
    [IsFiniteMeasure μ] (H' : Subgroup H) (hH' : MeasurableSet (H' : Set H))
    [Fintype (H ⧸ H')] (f : H → ℂ) (hf : ∀ h : H, ∀ h' ∈ H', f (h * h') = f h) :
    ∫ h, f h ∂μ = ∑ x : H ⧸ H', (μ.real (H' : Set H) : ℂ) * f (Quotient.out x) := by
  classical
  have hcoset : ∀ x : H ⧸ H', (QuotientGroup.mk ⁻¹' {x} : Set H) =
      (fun h => (Quotient.out x)⁻¹ * h) ⁻¹' (H' : Set H) := by
    intro x
    ext h
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    conv_lhs => rw [← QuotientGroup.out_eq' x]
    rw [eq_comm, QuotientGroup.eq]
  have hmeas : ∀ x : H ⧸ H', MeasurableSet (QuotientGroup.mk ⁻¹' {x} : Set H) := by
    intro x
    rw [hcoset x]
    exact (measurable_const_mul _) hH'
  have hmass : ∀ x : H ⧸ H', μ.real (QuotientGroup.mk ⁻¹' {x} : Set H) =
      μ.real (H' : Set H) := by
    intro x
    rw [hcoset x, Measure.real, Measure.real, measure_preimage_mul]
  have hconst : ∀ h : H, f h = f (Quotient.out (QuotientGroup.mk h : H ⧸ H')) := by
    intro h
    have h1 : h⁻¹ * Quotient.out (QuotientGroup.mk h : H ⧸ H') ∈ H' := by
      rw [← QuotientGroup.eq]
      exact (QuotientGroup.out_eq' _).symm
    rw [← hf h _ h1, mul_inv_cancel_left]
  have hsum : (fun h => f h) = fun h => ∑ x : H ⧸ H',
      (QuotientGroup.mk ⁻¹' {x} : Set H).indicator (fun _ => f (Quotient.out x)) h := by
    funext h
    rw [Finset.sum_eq_single (QuotientGroup.mk h : H ⧸ H')]
    · rw [Set.indicator_of_mem (by simp), hconst h]
    · intro x _ hx
      rw [Set.indicator_of_notMem]
      simpa [eq_comm] using hx
    · simp
  rw [hsum, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro x _
    rw [integral_indicator_const _ (hmeas x), hmass x, Complex.real_smul]
  · intro x _
    exact (integrable_const _).indicator (hmeas x)

end CosetSum

section Automorphisms

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E]

/-- The entrywise action of `σ` on the Levi `B.Levi E`, as a topological group automorphism. -/
def leviContinuousAut (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n) : B.Levi E ≃ₜ* B.Levi E where
  toMulEquiv := leviAut σ B
  continuous_toFun := continuous_pi fun i =>
    (continuous_entrywiseAut σ (B.size i)).comp (continuous_apply i)
  continuous_invFun := continuous_pi fun i =>
    (continuous_entrywiseAut_symm σ (B.size i)).comp (continuous_apply i)

@[simp]
theorem leviContinuousAut_apply (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n) (m : B.Levi E) :
    leviContinuousAut σ B m = leviAut σ B m := rfl

/-- The entrywise action of `σ` on the unipotent radical. -/
def unipotentContinuousAut (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n) :
    B.unipotentSubgroup E ≃ₜ* B.unipotentSubgroup E where
  toFun y := ⟨entrywiseAut σ n y, (entrywiseAut_mem_unipotentSubgroup_iff σ B y).mpr y.property⟩
  invFun y := ⟨entrywiseAut σ.symm n y,
    (entrywiseAut_mem_unipotentSubgroup_iff σ.symm B y).mpr y.property⟩
  left_inv y := Subtype.ext ((entrywiseAut σ n).symm_apply_apply (y : GeneralLinear n E))
  right_inv y := Subtype.ext ((entrywiseAut σ n).apply_symm_apply (y : GeneralLinear n E))
  map_mul' y z := Subtype.ext (map_mul (entrywiseAut σ n) (y : GeneralLinear n E) z)
  continuous_toFun := ((continuous_entrywiseAut σ n).comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((continuous_entrywiseAut_symm σ n).comp continuous_subtype_val).subtype_mk _

@[simp]
theorem coe_unipotentContinuousAut (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n)
    (y : B.unipotentSubgroup E) :
    (unipotentContinuousAut σ B y : GeneralLinear n E) = entrywiseAut σ n y := rfl

theorem entrywiseAut_mem_integralGL (σ : E ≃ₐ[F] E) {n : ℕ} {k : GeneralLinear n E}
    (hk : k ∈ integralGL E n) : entrywiseAut σ n k ∈ integralGL E n :=
  (entrywiseAut_mem_integralGL_iff σ k).mpr hk

/-- The entrywise action of `σ` on `GL_n(𝒪_E)`. -/
def integralContinuousAut (σ : E ≃ₐ[F] E) (n : ℕ) : integralGL E n ≃ₜ* integralGL E n where
  toFun k := ⟨entrywiseAut σ n (k : GeneralLinear n E), entrywiseAut_mem_integralGL σ k.property⟩
  invFun k := ⟨entrywiseAut σ.symm n (k : GeneralLinear n E),
    entrywiseAut_mem_integralGL σ.symm k.property⟩
  left_inv k := Subtype.ext ((entrywiseAut σ n).symm_apply_apply (k : GeneralLinear n E))
  right_inv k := Subtype.ext ((entrywiseAut σ n).apply_symm_apply (k : GeneralLinear n E))
  map_mul' k k' := Subtype.ext (map_mul (entrywiseAut σ n) (k : GeneralLinear n E) k')
  continuous_toFun := ((continuous_entrywiseAut σ n).comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((continuous_entrywiseAut_symm σ n).comp continuous_subtype_val).subtype_mk _

@[simp]
theorem coe_integralContinuousAut (σ : E ≃ₐ[F] E) (n : ℕ) (k : integralGL E n) :
    (integralContinuousAut σ n k : GeneralLinear n E) = entrywiseAut σ n k := rfl

attribute [local instance] LocalFieldTopology.generalLinear_t2Space
  LocalFieldTopology.generalLinear_locallyCompactSpace
  LocalFieldTopology.generalLinear_secondCountableTopology

variable (σ : E ≃ₐ[F] E) {n : ℕ} (B : BlockShape n)

/-- Haar measure on `GL_n(E)` is invariant under the entrywise action of `σ`. -/
theorem map_entrywiseAut_eq [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
    (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure] :
    μ.map (entrywiseContinuousAut σ n) = μ :=
  map_eq_self_of_preimage_eq μ _ (isCompact_integralGL n) (isOpen_integralGL n)
    ⟨1, (integralGL E n).one_mem⟩ (Set.ext fun g => entrywiseAut_mem_integralGL_iff σ g)

/-- Haar measure on the Levi is invariant under the entrywise action of `σ`. -/
theorem map_leviAut_eq [MeasurableSpace (B.Levi E)] [BorelSpace (B.Levi E)]
    (μ : Measure (B.Levi E)) [μ.IsHaarMeasure] :
    μ.map (leviContinuousAut σ B) = μ := by
  have hpi : {x : B.Levi E | ∀ i, x i ∈ integralGL E (B.size i)} =
      Set.univ.pi fun i => (integralGL E (B.size i) : Set (GeneralLinear (B.size i) E)) := by
    ext x
    simp
  refine map_eq_self_of_preimage_eq μ _ (C := {x : B.Levi E | ∀ i, x i ∈ integralGL E (B.size i)})
    ?_ ?_ ⟨1, fun i => (integralGL E (B.size i)).one_mem⟩ ?_
  · rw [hpi]
    exact isCompact_univ_pi fun i => isCompact_integralGL (B.size i)
  · rw [hpi]
    exact isOpen_set_pi Set.finite_univ fun i _ => isOpen_integralGL (B.size i)
  · ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, leviContinuousAut_apply, leviAut_apply,
      entrywiseAut_mem_integralGL_iff]

/-- Haar measure on the unipotent radical is invariant under the entrywise action of `σ`. -/
theorem map_unipotentAut_eq [MeasurableSpace (GeneralLinear n E)]
    [BorelSpace (GeneralLinear n E)] (μ : Measure (B.unipotentSubgroup E)) [μ.IsHaarMeasure] :
    μ.map (unipotentContinuousAut σ B) = μ := by
  have hcl : IsClosed (B.unipotentSubgroup E : Set (GeneralLinear n E)) :=
    B.isClosed_unipotentSubgroup E
  have : LocallyCompactSpace (B.unipotentSubgroup E) :=
    hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (B.unipotentSubgroup E) :=
    inferInstanceAs (SecondCountableTopology (B.unipotentSubgroup E : Set (GeneralLinear n E)))
  refine map_eq_self_of_preimage_eq μ _
    (C := {y : B.unipotentSubgroup E | (y : GeneralLinear n E) ∈ integralGL E n})
    (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_integralGL n))
    ((isOpen_integralGL n).preimage continuous_subtype_val) ⟨1, (integralGL E n).one_mem⟩ ?_
  ext y
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, coe_unipotentContinuousAut,
    entrywiseAut_mem_integralGL_iff]

/-- Haar measure on `GL_n(𝒪_E)` is invariant under the entrywise action of `σ`. -/
theorem map_integralAut_eq [MeasurableSpace (GeneralLinear n E)]
    [BorelSpace (GeneralLinear n E)] (μ : Measure (integralGL E n)) [μ.IsHaarMeasure] :
    μ.map (integralContinuousAut σ n) = μ := by
  have : CompactSpace (integralGL E n) := isCompact_iff_compactSpace.mp (isCompact_integralGL n)
  have : SecondCountableTopology (integralGL E n) :=
    inferInstanceAs (SecondCountableTopology (integralGL E n : Set (GeneralLinear n E)))
  exact map_eq_self_of_preimage_eq μ _ isCompact_univ isOpen_univ ⟨1, trivial⟩ rfl

end Automorphisms

section Iwasawa

variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] {n : ℕ} (B : BlockShape n)

attribute [local instance] LocalFieldTopology.t2Space
  LocalFieldTopology.generalLinear_t2Space
  LocalFieldTopology.generalLinear_locallyCompactSpace
  LocalFieldTopology.generalLinear_secondCountableTopology

/-- The unipotent radical is second countable. -/
theorem unipotentSubgroup_secondCountable :
    SecondCountableTopology (B.unipotentSubgroup E) :=
  inferInstanceAs (SecondCountableTopology (B.unipotentSubgroup E : Set (GeneralLinear n E)))

/-- The unipotent radical is locally compact. -/
theorem unipotentSubgroup_locallyCompact : LocallyCompactSpace (B.unipotentSubgroup E) :=
  (B.isClosed_unipotentSubgroup E).isClosedEmbedding_subtypeVal.locallyCompactSpace

/-- The standard parabolic is second countable. -/
theorem parabolic_secondCountable : SecondCountableTopology (B.parabolic E) :=
  inferInstanceAs (SecondCountableTopology (B.parabolic E : Set (GeneralLinear n E)))

/-- The standard parabolic is locally compact. -/
theorem parabolic_locallyCompact : LocallyCompactSpace (B.parabolic E) :=
  (B.isClosed_parabolic E).isClosedEmbedding_subtypeVal.locallyCompactSpace

/-- `GL_n(𝒪_E)` is compact. -/
theorem integralGL_compactSpace (n : ℕ) : CompactSpace (integralGL E n) :=
  isCompact_iff_compactSpace.mp (isCompact_integralGL n)

/-- `GL_n(𝒪_E)` is second countable. -/
theorem integralGL_secondCountable (n : ℕ) : SecondCountableTopology (integralGL E n) :=
  inferInstanceAs (SecondCountableTopology (integralGL E n : Set (GeneralLinear n E)))

attribute [local instance] unipotentSubgroup_secondCountable unipotentSubgroup_locallyCompact
  parabolic_secondCountable parabolic_locallyCompact integralGL_compactSpace
  integralGL_secondCountable

variable [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  [MeasurableSpace (B.Levi E)] [BorelSpace (B.Levi E)]

/-- The measure `dm du` on the parabolic, pushed forward along `(m, u) ↦ m u`. -/
def parabolicHaar (μM : Measure (B.Levi E)) (μU : Measure (B.unipotentSubgroup E)) :
    Measure (B.parabolic E) :=
  (μM.prod μU).map (parabolicProduct B)

theorem measurable_parabolicProduct : Measurable (parabolicProduct (R := E) B) :=
  (continuous_parabolicProduct (R := E) B).measurable

/-- `dm du` is a left Haar measure on the parabolic. -/
theorem parabolicHaar_isHaarMeasure (μM : Measure (B.Levi E)) [μM.IsHaarMeasure]
    (μU : Measure (B.unipotentSubgroup E)) [μU.IsHaarMeasure] :
    (parabolicHaar B μM μU).IsHaarMeasure := by
  have hΦ : ⇑(parabolicProductHomeomorph (R := E) B) = parabolicProduct B := rfl
  have hfin : IsFiniteMeasureOnCompacts (parabolicHaar B μM μU) := by
    have := IsFiniteMeasureOnCompacts.map (μM.prod μU) (parabolicProductHomeomorph (R := E) B)
    rwa [hΦ] at this
  have hopen : (parabolicHaar B μM μU).IsOpenPosMeasure := by
    have := (parabolicProductHomeomorph (R := E) B).continuous.isOpenPosMeasure_map
      (μ := μM.prod μU) (parabolicProductHomeomorph (R := E) B).surjective
    rwa [hΦ] at this
  have hleft : (parabolicHaar B μM μU).IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    obtain ⟨x₀, rfl⟩ := (parabolicProductEquiv (R := E) B).surjective g
    let c : B.Levi E → B.unipotentSubgroup E := fun m =>
      ⟨(B.leviEmbedding E m)⁻¹ * x₀.2 * B.leviEmbedding E m,
        leviEmbedding_conj_mem_unipotentSubgroup B m x₀.2.property⟩
    have hc : Continuous c := by
      refine Continuous.subtype_mk ?_ _
      have h1 : Continuous fun m : B.Levi E => B.leviEmbedding E m :=
        (B.leviEmbeddingContinuous E).continuous
      exact (h1.inv.mul continuous_const).mul h1
    have hT : MeasurePreserving (fun x : B.Levi E × B.unipotentSubgroup E =>
        (x₀.1 * x.1, c x.1 * x.2)) (μM.prod μU) (μM.prod μU) := by
      refine MeasurePreserving.skew_product (μa := μM) (μb := μM) (μc := μU) (μd := μU)
        (g := fun m y => c m * y) (measurePreserving_mul_left μM x₀.1) ?_ ?_
      · exact ((hc.comp continuous_fst).mul continuous_snd).measurable
      · exact Filter.Eventually.of_forall fun m => map_mul_left_eq_self μU (c m)
    have hcomp : (fun p => parabolicProductEquiv (R := E) B x₀ * p) ∘ parabolicProduct B =
        parabolicProduct B ∘ (fun x : B.Levi E × B.unipotentSubgroup E =>
          (x₀.1 * x.1, c x.1 * x.2)) := by
      funext x
      exact parabolicProduct_mul B x₀ x
    unfold parabolicHaar
    rw [Measure.map_map (measurable_const_mul _) (measurable_parabolicProduct B), hcomp,
      ← Measure.map_map (measurable_parabolicProduct B) hT.measurable, hT.map_eq]
  exact { }

/-- The Iwasawa decomposition `dg = dm du dk` with Henniart–Lemaire's normalizations. -/
theorem iwasawa_measure_eq (μG : Measure (GeneralLinear n E)) [μG.IsHaarMeasure]
    (μM : Measure (B.Levi E)) [μM.IsHaarMeasure]
    (μU : Measure (B.unipotentSubgroup E)) [μU.IsHaarMeasure]
    (μK : Measure (integralGL E n)) [μK.IsHaarMeasure] [IsProbabilityMeasure μK]
    (hG : μG (integralGL E n) = 1)
    (hM : μM {x | ∀ i, x i ∈ integralGL E (B.size i)} = 1)
    (hU : μU {y | (y : GeneralLinear n E) ∈ integralGL E n} = 1) :
    μG = ((μM.prod μU).prod μK).map
      (fun x => B.leviEmbedding E x.1.1 * (x.1.2 : GeneralLinear n E) *
        (x.2 : GeneralLinear n E)) := by
  have := parabolicHaar_isHaarMeasure B μM μU
  obtain ⟨c, hc, h⟩ := CompactFactorization.exists_pos_eq_smul_map_mul_prod μG (B.parabolic E)
    (B.isClosed_parabolic E) (integralGL E n) (isCompact_integralGL n)
    (fun g => exists_parabolic_mul_integralGL B g) (parabolicHaar B μM μU) μK
  have hmeasF : Measurable (fun x : (B.Levi E × B.unipotentSubgroup E) × integralGL E n =>
      B.leviEmbedding E x.1.1 * (x.1.2 : GeneralLinear n E) * (x.2 : GeneralLinear n E)) :=
    ((((B.leviEmbeddingContinuous E).continuous.comp (continuous_fst.comp continuous_fst)).mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))).mul
      (continuous_subtype_val.comp continuous_snd)).measurable
  have hprod : (parabolicHaar B μM μU).prod μK =
      ((μM.prod μU).prod μK).map (Prod.map (parabolicProduct B) id) := by
    unfold parabolicHaar
    conv_lhs => rw [← Measure.map_id (μ := μK)]
    exact Measure.map_prod_map _ _ (measurable_parabolicProduct B) measurable_id
  have hmul : Measurable (fun p : B.parabolic E × integralGL E n =>
      (p.1 : GeneralLinear n E) * p.2) :=
    (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd) |>.measurable
  rw [hprod, Measure.map_map hmul
    ((measurable_parabolicProduct B).prodMap measurable_id)] at h
  have hfun : (fun p : B.parabolic E × integralGL E n => (p.1 : GeneralLinear n E) * p.2) ∘
      Prod.map (parabolicProduct B) id =
      fun x : (B.Levi E × B.unipotentSubgroup E) × integralGL E n =>
        B.leviEmbedding E x.1.1 * (x.1.2 : GeneralLinear n E) * (x.2 : GeneralLinear n E) := by
    funext x
    rfl
  rw [hfun] at h
  -- Evaluate both sides on `K`.
  have hpre : (fun x : (B.Levi E × B.unipotentSubgroup E) × integralGL E n =>
      B.leviEmbedding E x.1.1 * (x.1.2 : GeneralLinear n E) * (x.2 : GeneralLinear n E)) ⁻¹'
        (integralGL E n : Set (GeneralLinear n E)) =
      ({x : B.Levi E | ∀ i, x i ∈ integralGL E (B.size i)} ×ˢ
        {y : B.unipotentSubgroup E | (y : GeneralLinear n E) ∈ integralGL E n}) ×ˢ Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_ofPred_eq, Set.mem_univ, and_true,
      SetLike.mem_coe]
    rw [← leviEmbedding_mul_mem_integralGL_iff]
    constructor
    · intro h
      have := (integralGL E n).mul_mem h ((integralGL E n).inv_mem x.2.property)
      rwa [mul_inv_cancel_right] at this
    · intro h
      exact (integralGL E n).mul_mem h x.2.property
  have hνK : (((μM.prod μU).prod μK).map
      (fun x : (B.Levi E × B.unipotentSubgroup E) × integralGL E n =>
        B.leviEmbedding E x.1.1 * (x.1.2 : GeneralLinear n E) * (x.2 : GeneralLinear n E)))
        (integralGL E n) = 1 := by
    rw [Measure.map_apply hmeasF (isOpen_integralGL n).measurableSet, hpre,
      Measure.prod_prod, Measure.prod_prod, hM, hU, measure_univ, one_mul, one_mul]
  have hc1 : (c : ℝ≥0∞) = 1 := by
    have := congrArg (fun μ : Measure (GeneralLinear n E) => μ (integralGL E n)) h
    simp only [Measure.smul_apply] at this
    rw [hG, hνK, ENNReal.smul_def, smul_eq_mul, mul_one] at this
    exact this.symm
  have hc1' : c = 1 := by exact_mod_cast hc1
  rw [h, hc1', one_smul]

end Iwasawa

end Langlands.BaseChange.TwistedVanDijk
