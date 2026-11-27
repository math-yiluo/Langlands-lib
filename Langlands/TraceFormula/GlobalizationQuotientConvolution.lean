import Langlands.Global.PositiveQuotientL2UnfoldingProof
import Langlands.Global.AdelicSplitCenterHaar
import Langlands.Analysis.Local.QuotientProductFactor
import Langlands.Automorphic.GroupSchemeQuotientL2Integrated
import Langlands.Representation.Unitary.IntegratedTranslationPointwiseProof

/-! # Compact convolution on the positive rational quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Filter Topology
open scoped CategoryTheory.MonObj CompactlySupported
open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions Langlands.QuotientIntegration

namespace Langlands.TraceFormula

variable (K : Type u) [Field K] [NumberField K]
  (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of K))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup K G)).IsMulRightInvariant]

local notation "A" => AdelicGroupPoints K G
local notation "N" => normOneSubgroup K G
local notation "Γ" => positiveRationalSubgroup K G T i
local notation "Q" => PositiveRationalQuotient K G T i
local notation "ν" => positiveRationalQuotientHaarMeasure K G T i
local notation "μG" => (Measure.haar : Measure A)
local notation "π" => haarQuotientL2BoundedRightAction K G T i hi I e hc
local notation "R" => haarQuotientL2IntegratedAction K G T i hi I e hc μG

/-- Integrating a compact test against one fixed orbit is linear in the test. -/
def positiveQuotientCompactConvolution (φ : Lp ℂ 2 ν) : C_c(A, ℂ) →ₗ[ℂ] Lp ℂ 2 ν := by
  let h (f : C_c(A, ℂ)) : Integrable f μG :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  refine
    { toFun := fun f => R f (h f) φ
      map_add' := fun f g => ?_
      map_smul' := fun r f => ?_ }
  · change (∫ a, ((f a + g a) • π a φ) ∂μG) =
      (∫ a, f a • π a φ ∂μG) + ∫ a, g a • π a φ ∂μG
    simpa only [add_smul, haarQuotientL2BoundedRightAction_apply] using integral_add
      (haarQuotientL2ActionIntegrand_integrable K G T i hi I e hc μG f (h f) φ)
      (haarQuotientL2ActionIntegrand_integrable K G T i hi I e hc μG g (h g) φ)
  · change (∫ a, (r • f a) • π a φ ∂μG) = r • ∫ a, f a • π a φ ∂μG
    simp only [smul_assoc, integral_smul]

/-- Left translating the convolution weight acts by the original quotient representation. -/
theorem positiveQuotientCompactConvolution_leftTranslate (φ : Lp ℂ 2 ν)
    (f f' : C_c(A, ℂ)) (a : A) (h : ∀ g, f' g = f (a⁻¹ * g)) :
    positiveQuotientCompactConvolution K G T i hi I e hc φ f' =
      π a (positiveQuotientCompactConvolution K G T i hi I e hc φ f) := by
  change (∫ g, f' g • π g φ ∂μG) = π a (∫ g, f g • π g φ ∂μG)
  have hf : Integrable (fun g => f g • π g φ) μG := by
    simpa only [haarQuotientL2BoundedRightAction_apply] using
      haarQuotientL2ActionIntegrand_integrable K G T i hi I e hc μG f
        (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport) φ
  rw [← (π a).integral_comp_comm hf, ← integral_mul_left_eq_self («μ» := μG)
    (fun g => f' g • π g φ) a]
  apply integral_congr_ae (Eventually.of_forall fun g => ?_)
  rw [h, inv_mul_cancel_left, map_smul, map_mul, mul_apply_eq_comp]

private theorem compactConvolution_continuousRepresentative
    (f : C_c(A, ℂ)) {φ : Q → ℂ} (hφ : Continuous φ) (hm : MemLp φ 2 ν) :
    let Ψ : Q → ℂ := fun q => ∫ a, f a * φ (LeftCosetSpace.rightTranslate Γ a q) ∂μG
    Continuous Ψ ∧
      (positiveQuotientCompactConvolution K G T i hi I e hc (hm.toLp φ) f : Q → ℂ) =ᵐ[ν] Ψ := by
  let : T2Space Q := positiveRationalQuotient_t2Space K G T i hi I e hc
  let : BorelSpace Q := positiveRationalQuotient_borelSpace K G T i hi I e hc
  let : SecondCountableTopology Q :=
    TopologicalSpace.Quotient.secondCountableTopology (LeftCosetSpace.isOpenQuotientMap_mk Γ).isOpenMap
  let : (ν).Regular := positiveRationalQuotientHaarMeasure_regular K G T i hi I e hc
  let : IsLocallyFiniteMeasure ν :=
    positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure K G T i hi I e hc
  let act (q : Q) (a : A) := LeftCosetSpace.rightTranslate Γ a q
  have hact : Continuous (Function.uncurry act) := by
    let hq := LeftCosetSpace.isOpenQuotientMap_mk Γ
    rw [(hq.prodMap IsOpenQuotientMap.id).isQuotientMap.continuous_iff]
    exact hq.continuous.comp (continuous_fst.mul continuous_snd)
  let Ψ (q : Q) := ∫ a, f a * φ (act q a) ∂μG
  change Continuous Ψ ∧ _
  refine ⟨?_, ?_⟩
  · rw [← continuousOn_univ]
    apply continuousOn_integral_of_compact_support f.hasCompactSupport
    · exact ((f.continuous.comp continuous_snd).mul (hφ.comp hact)).continuousOn
    · intro q a _ ha
      exact mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport ha) _
  · have hpres := haarQuotientMeasureRightInvariant K G T i hi I e hc
    have hpt := (Langlands.Analysis.integratedTranslationPointwise Q ν A μG act hact.measurable
      hpres π (norm_haarQuotientL2BoundedRightAction K G T i hi I e hc)
      (haarQuotientL2Orbit_aestronglyMeasurable K G T i hi I e hc μG)
      (coeFn_quotientL2RightTranslate K G T i ν hpres) f
      (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport) (hm.toLp φ)).2
    have hcomp₁ := (Lp.stronglyMeasurable (hm.toLp φ)).comp_measurable hact.measurable
    have hcomp₂ := hφ.stronglyMeasurable.comp_measurable hact.measurable
    have hcomp : ∀ᵐ q ∂ν, ∀ᵐ a ∂μG, hm.toLp φ (act q a) = φ (act q a) :=
      (Measure.ae_ae_comm (hcomp₁.measurableSet_eq_fun hcomp₂)).mpr
        (Eventually.of_forall fun a => (hpres a).quasiMeasurePreserving.ae_eq_comp hm.coeFn_toLp)
    filter_upwards [hpt, hcomp] with q hq hq'
    exact hq.trans (integral_congr_ae (hq'.mono fun a ha => congrArg (fun z => f a * z) ha))

/-- Average a full compact test in the positive central factor using the Haar normalization
for the exact full-group product formula. -/
def globalizationNormOneAverage (f : C_c(A, ℂ)) : C_c(N, ℂ) := by
  let μA := normalizedPositiveHaarMeasure K G T i hi I e hc
  let : μA.IsHaarMeasure := normalizedPositiveHaarMeasure_isHaarMeasure K G T i hi I e hc
  exact compactIntegralFullFactor _ μA
    (f.comp (normOneDecomposition K G T i hi I e).toCocompactMap)

omit [(Measure.haar : Measure N).IsMulRightInvariant] in
@[simp] theorem globalizationNormOneAverage_apply (f : C_c(A, ℂ)) (n : N) :
    globalizationNormOneAverage K G T i hi I e hc f n =
      ∫ a : intrinsicSubgroup K T, f (positivePointMap K G T i a * n.val)
        ∂normalizedPositiveHaarMeasure K G T i hi I e hc := rfl

omit [(Measure.haar : Measure N).IsMulRightInvariant] in
/-- A test with nonnegative real part along the positive subgroup and positive real part
at one has nonzero positive average at the norm-one identity. -/
theorem globalizationNormOneAverage_one_ne_zero (f : C_c(A, ℂ))
    (hnonneg : ∀ a : intrinsicSubgroup K T, 0 ≤ (f (positivePointMap K G T i a)).re)
    (h₁ : (f 1).re ≠ 0) : globalizationNormOneAverage K G T i hi I e hc f 1 ≠ 0 := by
  let μA := normalizedPositiveHaarMeasure K G T i hi I e hc
  let : μA.IsHaarMeasure := normalizedPositiveHaarMeasure_isHaarMeasure K G T i hi I e hc
  let p : intrinsicSubgroup K T → A := positivePointMap K G T i
  have hp : IsClosedEmbedding p := by
    let j : intrinsicSubgroup K T → intrinsicSubgroup K T × N := fun a => (a, 1)
    have hj : IsClosedEmbedding j := ⟨isEmbedding_prodMkLeft (1 : N), by
      have he : Set.range j = Prod.snd ⁻¹' {(1 : N)} := by
        ext z
        simp [j, Prod.ext_iff, eq_comm]
      rw [he]
      exact isClosed_singleton.preimage continuous_snd⟩
    have h := (normOneDecomposition K G T i hi I e).isClosedEmbedding.comp hj
    have he : normOneDecomposition K G T i hi I e ∘ j = p := by
      funext a
      simp [j, p]
    exact he ▸ h
  have hf : Integrable (fun a => f (p a)) μA :=
    (f.continuous.comp hp.continuous).integrable_of_hasCompactSupport
      (f.hasCompactSupport.comp_isClosedEmbedding hp)
  have h0 : (f (p 1)).re ≠ 0 := by simpa only [p, map_one] using h₁
  have hpos : 0 < ∫ a, (f (p a)).re ∂μA :=
    integral_pos_of_integrable_nonneg_nonzero (Complex.continuous_re.comp (f.continuous.comp hp.continuous))
      hf.re hnonneg (x := 1) h0
  intro hz
  have hz' := congrArg Complex.re hz
  simp only [globalizationNormOneAverage_apply, Subgroup.coe_one, mul_one, Complex.zero_re] at hz'
  exact hpos.ne' ((integral_re hf).trans hz')

private theorem integral_weight_mul_pullback (f : C_c(A, ℂ)) {φ : Q → ℂ} (hφ : Continuous φ) :
    (∫ g, f g * φ (LeftCosetSpace.mk Γ g) ∂μG) =
      ∫ q, positiveNormOneQuotientAverage K G T i hi I e hc
        (globalizationNormOneAverage K G T i hi I e hc f) q * φ q ∂ν := by
  let b := globalizationNormOneAverage K G T i hi I e hc f
  let h (g : A) := f g * φ (LeftCosetSpace.mk Γ g)
  have hh : Integrable h μG := (f.continuous.mul
    (hφ.comp (LeftCosetSpace.continuous_mk Γ))).integrable_of_hasCompactSupport
      f.hasCompactSupport.mul_right
  let k (n : N) := b n * φ (LeftCosetSpace.mk Γ n.val)
  have hk : Continuous k := b.continuous.mul
    (hφ.comp ((LeftCosetSpace.continuous_mk Γ).comp continuous_subtype_val))
  have hkc : HasCompactSupport k := b.hasCompactSupport.mul_right
  calc
    _ = ∫ n, k n ∂Measure.haar := by
      rw [show (fun g => f g * φ (LeftCosetSpace.mk Γ g)) = h from rfl,
        integral_normOneDecomposition_fubini_symm K G T i hi I e hc h hh]
      apply integral_congr_ae (Eventually.of_forall fun n => ?_)
      have hp (a : intrinsicSubgroup K T) :
          LeftCosetSpace.mk Γ (positivePointMap K G T i a * n.val) = LeftCosetSpace.mk Γ n.val :=
        LeftCosetSpace.mk_subgroup_mul Γ
          ⟨_, imageSubgroup_le_positiveRationalSubgroup K G T i ⟨a.val, a.property, rfl⟩⟩ n.val
      simp only [h, k, hp, integral_mul_const, b, globalizationNormOneAverage_apply]
    _ = _ := by
      rw [← integral_positiveNormOneQuotientAverage K G T i hi I e hc k hk hkc]
      apply integral_congr_ae (Eventually.of_forall fun q => ?_)
      obtain ⟨p, rfl⟩ := (positiveQuotientHomeomorph K G T i hi I e hc).surjective q
      change positiveNormOneQuotientAverage K G T i hi I e hc k
          (normOneToPositiveQuotient K G T i p) =
        positiveNormOneQuotientAverage K G T i hi I e hc b (normOneToPositiveQuotient K G T i p) *
          φ (normOneToPositiveQuotient K G T i p)
      let Λ := rationalNormOneSubgroup K G
      obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective Λ p
      simp only [positiveNormOneQuotientAverage_normOneToPositiveQuotient]
      change (∫ γ : Λ, k (γ.val * x) ∂Measure.count) =
        (∫ γ : Λ, b (γ.val * x) ∂Measure.count) * φ (LeftCosetSpace.mk Γ x.val)
      have hγ (γ : Λ) : LeftCosetSpace.mk Γ (γ.val * x).val = LeftCosetSpace.mk Γ x.val :=
        LeftCosetSpace.mk_subgroup_mul Γ
          ⟨_, rationalSubgroup_le_positiveRationalSubgroup K G T i
            (rationalNormOneSubgroupInclusion K G γ).property⟩ x.val
      simp only [k, hγ, integral_mul_const]

private theorem integral_mul_star_ne_zero {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] {m : Measure X} [IsLocallyFiniteMeasure m] [m.IsOpenPosMeasure]
    {row : X → ℂ} (hc : Continuous row) (hs : HasCompactSupport row) {x : X} (hx : row x ≠ 0) :
    (∫ q, row q * star (row q) ∂m) ≠ 0 := by
  let r (q : X) := ‖row q‖ ^ 2
  have hr : Continuous r := hc.norm.pow 2
  have hrc : HasCompactSupport r := hs.mono fun q hq hzero => hq (by simp [r, hzero])
  have hp : 0 < ∫ q, r q ∂m := integral_pos_of_integrable_nonneg_nonzero hr
    (hr.integrable_of_hasCompactSupport hrc) (fun _ => sq_nonneg _) (x := x)
    (pow_ne_zero _ (norm_ne_zero_iff.mpr hx))
  have he : (∫ q, row q * star (row q) ∂m) = ((∫ q, r q ∂m : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae (Eventually.of_forall fun q => ?_)
    change row q * (starRingEnd ℂ) (row q) = ((‖row q‖ ^ 2 : ℝ) : ℂ)
    push_cast
    exact Complex.mul_conj' (row q)
  exact fun hz => hp.ne' (Complex.ofReal_eq_zero.mp (he.symm.trans hz))

set_option maxHeartbeats 1100000 in
/-- A nonzero value of the periodized positive average at the identity detects a nonzero
quotient convolution. The input is the conjugate periodization, so evaluation at the
identity is the integral of a squared norm. -/
theorem exists_positiveQuotientCompactConvolution_ne_zero (f : C_c(A, ℂ))
    (h : quotientAverage (rationalNormOneSubgroup K G) Measure.count
      (globalizationNormOneAverage K G T i hi I e hc f)
      (LeftCosetSpace.mk (rationalNormOneSubgroup K G) 1) ≠ 0) :
    ∃ φ : Lp ℂ 2 ν, positiveQuotientCompactConvolution K G T i hi I e hc φ f ≠ 0 := by
  let : T2Space Q := positiveRationalQuotient_t2Space K G T i hi I e hc
  let : BorelSpace Q := positiveRationalQuotient_borelSpace K G T i hi I e hc
  let : IsLocallyFiniteMeasure ν :=
    positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure K G T i hi I e hc
  let : (ν).IsOpenPosMeasure := haarQuotientMeasure_isOpenPosMeasure K G T i hi I e hc
  let b := globalizationNormOneAverage K G T i hi I e hc f
  let row := positiveNormOneQuotientAverage K G T i hi I e hc b
  obtain ⟨hrow, hrowc, -⟩ := positiveQuotientL2Unfolding K G T i hi I e hc b
  let q₀ := LeftCosetSpace.mk Γ 1
  have hrow₀ : row q₀ ≠ 0 := by
    change row (normOneToPositiveQuotient K G T i (LeftCosetSpace.mk (rationalNormOneSubgroup K G) 1)) ≠ 0
    simpa only [row, b, positiveNormOneQuotientAverage_normOneToPositiveQuotient] using h
  let φ (q : Q) := star (row q)
  have hφ : Continuous φ := hrow.star
  have hm : MemLp φ 2 ν := hφ.memLp_of_hasCompactSupport (hrowc.comp_left (star_zero _))
  refine ⟨hm.toLp φ, fun hzero => ?_⟩
  obtain ⟨hΨ, hΨae⟩ := compactConvolution_continuousRepresentative K G T i hi I e hc f hφ hm
  let Ψ (q : Q) := ∫ a, f a * φ (LeftCosetSpace.rightTranslate Γ a q) ∂μG
  have hzae : Ψ =ᵐ[ν] 0 := hΨae.symm.trans
    (by rw [hzero]; exact Lp.coeFn_zero ℂ 2 ν)
  have hz : Ψ q₀ = 0 := congrFun (Measure.eq_of_ae_eq hzae hΨ continuous_const) q₀
  have hq (a : A) : LeftCosetSpace.rightTranslate Γ a q₀ = LeftCosetSpace.mk Γ a := by
    change LeftCosetSpace.mk Γ (1 * a) = _
    rw [one_mul]
  have hvalue : Ψ q₀ = ∫ q, row q * star (row q) ∂ν := by
    change (∫ a, f a * φ (LeftCosetSpace.rightTranslate Γ a q₀) ∂μG) = _
    simp only [hq]
    exact integral_weight_mul_pullback K G T i hi I e hc f hφ
  exact integral_mul_star_ne_zero hrow hrowc hrow₀ (hvalue.symm.trans hz)

end Langlands.TraceFormula
