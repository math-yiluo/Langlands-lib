import Langlands.TraceFormula.GroupSchemeCuspidalImageStatement
import Langlands.TraceFormula.TwistedKernelOperator
import Langlands.Global.AdelicConstantTermAverage
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! # Cuspidal image of convolution on the positive adelic quotient -/

noncomputable section

universe u

open MeasureTheory Set Topology
open scoped CompactlySupported ENNReal

namespace Langlands.TraceFormula

open Langlands.Global Langlands.QuotientIntegration

/-- Fold the convolution against a continuous invariant function over the discrete
subgroup, and unfold the radical period using the same orbit sum. -/
private theorem convolutionPeriod_zero
    {A : Type u} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]
    [LocallyCompactSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.IsHaarMeasure]
    (N : Subgroup A) (hN : IsClosed (N : Set A)) [SecondCountableTopology N]
    (Λ : Subgroup N) (hΛ : IsDiscrete (Λ : Set N))
    [BorelSpace (LeftCosetSpace Λ)] [CompactSpace (LeftCosetSpace Λ)]
    (dn : Measure N) [dn.IsMulLeftInvariant] [dn.IsInvInvariant] [IsFiniteMeasureOnCompacts dn]
    (f : C_c(A, ℂ)) (hf : ∀ a b : A, ∫ n : N, f (a * (n : A) * b) ∂dn = 0)
    (Φ : A → ℂ) (hΦ : Continuous Φ)
    (hΦinv : ∀ (δ : Λ) (b : A), Φ (((δ : N) : A) * b) = Φ b)
    (x : A) (p : LeftCosetSpace Λ → ℂ)
    (hp : ∀ n : N, p (LeftCosetSpace.mk Λ n) =
      ∫ a, f a * Φ (((n : A) * x) * a) ∂μ) :
    Integrable p (LeftCosetSpace.discreteQuotientMeasure Λ hΛ dn) ∧
      ∫ q, p q ∂LeftCosetSpace.discreteQuotientMeasure Λ hΛ dn = 0 := by
  let L := Λ.map N.subtype
  let latticeEquiv : Λ ≃* L := Λ.equivMapOfInjective N.subtype Subtype.val_injective
  have hL : IsDiscrete (L : Set A) := hΛ.image IsEmbedding.subtypeVal.isInducing
  let : DiscreteTopology L := SetLike.isDiscrete_iff_discreteTopology.mp hL
  let : Countable L := LeftCosetSpace.countable_of_isDiscrete L hL
  let : Countable Λ := LeftCosetSpace.countable_of_isDiscrete Λ hΛ
  let : LocallyCompactSpace N := hN.locallyCompactSpace
  let : BorelSpace (LeftCosetSpace L) := LeftCosetSpace.discreteQuotientBorelSpace L hL
  let : T2Space (LeftCosetSpace L) := leftQuotient_t2Space L (L.isClosed_of_isDiscrete hL)
  let : T2Space (LeftCosetSpace Λ) := leftQuotient_t2Space Λ (Λ.isClosed_of_isDiscrete hΛ)
  let ν := LeftCosetSpace.discreteQuotientMeasure L hL μ
  let νN := LeftCosetSpace.discreteQuotientMeasure Λ hΛ dn
  let : IsLocallyFiniteMeasure ν :=
    LeftCosetSpace.isLocallyFiniteMeasure_discreteQuotientMeasure L hL μ
  let : IsLocallyFiniteMeasure νN :=
    LeftCosetSpace.isLocallyFiniteMeasure_discreteQuotientMeasure Λ hΛ dn
  have hδ (δ : Λ) : (latticeEquiv δ : A) = ((δ : N) : A) := rfl
  have hΦL (δ : L) (b : A) : Φ ((δ : A) * b) = Φ b := by
    obtain ⟨γ, rfl⟩ := latticeEquiv.surjective δ
    rw [hδ, hΦinv]
  let φ := LeftCosetSpace.lift L Φ hΦL
  have hφ : Continuous φ := LeftCosetSpace.continuous_lift L Φ hΦL hΦ
  have hj (δ : Λ) : N.subtype (δ : N) ∈ L := Subgroup.mem_map_of_mem N.subtype δ.2
  let orbit := periodOrbitMap L Λ N.subtype hj x
  have horbit : Continuous orbit := continuous_periodOrbitMap L Λ N.subtype hj
    continuous_subtype_val x
  let θ := ContinuousMulEquiv.refl A
  have hθ (a : A) : θ a ∈ L ↔ a ∈ L := Iff.rfl
  let K (q : LeftCosetSpace Λ) (b : LeftCosetSpace L) : ℂ :=
    twistedQuotientKernel L θ (fun a ha => (hθ a).2 ha) f (orbit q) b * φ b
  have hK : Continuous (Function.uncurry K) :=
    ((continuous_uncurry_twistedQuotientKernel L θ θ.continuous
      (fun a ha => (hθ a).2 ha) f).comp
        ((horbit.comp continuous_fst).prodMk continuous_snd)).mul (hφ.comp continuous_snd)
  have hK_mk (n : N) (b : A) :
      K (LeftCosetSpace.mk Λ n) (LeftCosetSpace.mk L b) =
        (∑' δ : L, f (((n : A) * x)⁻¹ * δ * b)) * Φ b := rfl
  -- A compact set of lifts of the first quotient bounds the support in the second one.
  obtain ⟨D, hD, hDall⟩ := leftQuotient_exists_isCompact_image Λ
    (Λ.isClosed_of_isDiscrete hΛ) isCompact_univ
  let c (z : N × A) := LeftCosetSpace.mk L (((z.1 : A) * x) * z.2)
  have hc : Continuous c := (LeftCosetSpace.continuous_mk L).comp
    (((continuous_subtype_val.comp continuous_fst).mul_const x).mul continuous_snd)
  have hKsupport : HasCompactSupport (Function.uncurry K) := by
    apply HasCompactSupport.intro (isCompact_univ.prod ((hD.prod f.hasCompactSupport).image hc))
    rintro ⟨q, b⟩ hb
    have hq : q ∈ leftQuotientMap Λ '' D := by rw [hDall]; exact mem_univ _
    obtain ⟨n, hn, rfl⟩ := hq
    change twistedQuotientKernel L θ (fun a ha => (hθ a).2 ha) f
      (LeftCosetSpace.mk L ((n : A) * x)) b * φ b = 0
    apply mul_eq_zero_of_left
    apply twistedQuotientKernel_mk_eq_zero L θ hθ f ((n : A) * x) b
    rintro ⟨b', ⟨_, ⟨a, ha, rfl⟩, rfl⟩, hb'⟩
    exact hb ⟨mem_univ _, ⟨(n, a), ⟨hn, ha⟩, hb'⟩⟩
  have hKint : Integrable (Function.uncurry K) (νN.prod ν) :=
    hK.integrable_of_hasCompactSupport hKsupport
  -- Left translation of the Haar variable makes the continuous input independent of n.
  have hfold : p = fun q => ∫ b, K q b ∂ν := by
    funext q
    obtain ⟨n, rfl⟩ := LeftCosetSpace.mk_surjective Λ q
    let k (b : A) := f (((n : A) * x)⁻¹ * b) * Φ b
    have hkc : Continuous k :=
      (f.continuous.comp (continuous_const.mul continuous_id)).mul hΦ
    have hk : Integrable k μ := hkc.integrable_of_hasCompactSupport
      ((f.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft (((n : A) * x)⁻¹))).mul_right)
    have havg : LeftCosetSpace.automorphize L k = K (LeftCosetSpace.mk Λ n) := by
      funext q
      obtain ⟨b, rfl⟩ := LeftCosetSpace.mk_surjective L q
      rw [LeftCosetSpace.automorphize_mk, hK_mk]
      simp only [k, hΦL, ← mul_assoc, tsum_mul_right]
    have hrow : Continuous (K (LeftCosetSpace.mk Λ n)) :=
      hK.comp (continuous_const.prodMk continuous_id)
    rw [hp]
    calc ∫ a, f a * Φ (((n : A) * x) * a) ∂μ = ∫ b, k b ∂μ := by
          simpa only [k, inv_mul_cancel_left] using integral_mul_left_eq_self (μ := μ) k ((n : A) * x)
      _ = ∫ b, K (LeftCosetSpace.mk Λ n) b ∂ν := by
        rw [← havg]
        exact LeftCosetSpace.integral_eq_integral_automorphize L μ
          (LeftCosetSpace.isFundamentalDomain L hL μ) hk
          (havg.symm ▸ hrow.aestronglyMeasurable)
  -- Inversion of the lattice index identifies each column with the periodized radical slice.
  have hunfold (q : LeftCosetSpace L) : ∫ r, K r q ∂νN = 0 := by
    obtain ⟨b, rfl⟩ := LeftCosetSpace.mk_surjective L q
    let k (n : N) := f (x⁻¹ * (n : A)⁻¹ * b) * Φ b
    let d : A ≃ₜ A := (Homeomorph.inv A).trans
      ((Homeomorph.mulLeft x⁻¹).trans (Homeomorph.mulRight b))
    have hd : IsClosedEmbedding (fun n : N => d (n : A)) :=
      d.isClosedEmbedding.comp hN.isClosedEmbedding_subtypeVal
    have hk : Integrable k dn := by
      apply ((f.continuous.comp hd.continuous).mul continuous_const).integrable_of_hasCompactSupport
      apply HasCompactSupport.intro (hd.isCompact_preimage f.hasCompactSupport)
      intro n hn
      exact mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport hn) _
    have havg : LeftCosetSpace.automorphize Λ k = fun r => K r (LeftCosetSpace.mk L b) := by
      funext q
      obtain ⟨n, rfl⟩ := LeftCosetSpace.mk_surjective Λ q
      rw [LeftCosetSpace.automorphize_mk, hK_mk, ← tsum_mul_right]
      let e : Λ ≃ L := (Equiv.inv Λ).trans latticeEquiv.toEquiv
      rw [← e.tsum_eq (fun δ : L => f (((n : A) * x)⁻¹ * δ * b) * Φ b)]
      apply tsum_congr
      intro δ
      change k ((δ : N) * n) = f (((n : A) * x)⁻¹ * (latticeEquiv δ⁻¹ : A) * b) * Φ b
      rw [hδ]
      simp [k, mul_assoc]
    have hcol : Continuous (fun r => K r (LeftCosetSpace.mk L b)) :=
      hK.comp (continuous_id.prodMk continuous_const)
    rw [← havg]
    change (∫ r, LeftCosetSpace.automorphize Λ k r
      ∂LeftCosetSpace.quotientMeasure Λ dn (LeftCosetSpace.fundamentalDomain Λ hΛ)) = 0
    rw [← LeftCosetSpace.integral_eq_integral_automorphize Λ dn
      (LeftCosetSpace.isFundamentalDomain Λ hΛ dn) hk (havg.symm ▸ hcol.aestronglyMeasurable)]
    simp only [k, ← Subgroup.coe_inv, integral_mul_const]
    rw [integral_inv_eq_self (fun n : N => f (x⁻¹ * (n : A) * b)) dn, hf, zero_mul]
  rw [hfold]
  exact ⟨hKint.integral_prod_left, (integral_integral_swap hKint).trans
    (by simp_rw [hunfold, integral_zero])⟩

open scoped CategoryTheory.MonObj
open Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

/-- Vanishing of the translated radical integrals gives cuspidality on the
full positive-quotient `L²` space. -/
theorem groupSchemeCuspidalImage : GroupSchemeCuspidalImageStatement.{u} := by
  intro F _ _ G _ _ hPD hG T i hi _ I _ e hc _ μG f hf hvanish v
  let A := AdelicGroupPoints F G
  let Γ := positiveRationalSubgroup F G T i
  let Q := PositiveRationalQuotient F G T i
  let ν := positiveRationalQuotientHaarMeasure F G T i
  let : T2Space Q := positiveRationalQuotient_t2Space F G T i hi I e hc
  let : BorelSpace Q := positiveRationalQuotient_borelSpace F G T i hi I e hc
  let : SecondCountableTopology Q := (LeftCosetSpace.isOpenQuotientMap_mk Γ).secondCountableTopology
  let : ν.Regular := positiveRationalQuotientHaarMeasure_regular F G T i hi I e hc
  let : IsLocallyFiniteMeasure ν :=
    positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure F G T i hi I e hc
  let R := haarQuotientL2IntegratedAction F G T i hi I e hc μG f hf
  let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
  have hclosed : IsClosed (S : Set (Lp ℂ 2 ν)) :=
    (fullAEL2CuspidalClosedSubmodule F G hPD hG T i hi I e hc).isClosed
  -- Compactly supported continuous functions give density of classes with continuous representatives.
  let D : Set (Lp ℂ 2 ν) :=
    {w | ∃ (φ : Q → ℂ) (hφ : MemLp φ 2 ν), Continuous φ ∧ hφ.toLp φ = w}
  have hdense : Dense D := by
    intro w
    rw [EMetric.mem_closure_iff]
    intro ε hε
    obtain ⟨radius, hradius, hradius_lt⟩ := exists_between hε
    obtain ⟨φ, _, hdist, hφ, hm⟩ := (Lp.memLp w).exists_hasCompactSupport_eLpNorm_sub_le
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hradius.ne'
    refine ⟨hm.toLp φ, ⟨φ, hm, hφ, rfl⟩, ?_⟩
    rw [← Lp.toLp_coeFn w (Lp.memLp w), Lp.edist_toLp_toLp]
    exact hdist.trans_lt hradius_lt
  suffices hD : D ⊆ R ⁻¹' (S : Set (Lp ℂ 2 ν)) by
    exact closure_minimal hD (hclosed.preimage R.continuous) (hdense v)
  rintro _ ⟨φ, hm, hφ, rfl⟩
  let act (q : Q) (a : A) := LeftCosetSpace.rightTranslate Γ a q
  have hact : Continuous (Function.uncurry act) := by
    let hq := LeftCosetSpace.isOpenQuotientMap_mk Γ
    rw [(hq.prodMap IsOpenQuotientMap.id).isQuotientMap.continuous_iff]
    exact hq.continuous.comp (continuous_fst.mul continuous_snd)
  have hpres := haarQuotientMeasureRightInvariant F G T i hi I e hc
  let ψ (q : Q) := ∫ a, f a * φ (act q a) ∂μG
  have hψ : Continuous ψ := by
    rw [← continuousOn_univ]
    apply continuousOn_integral_of_compact_support f.hasCompactSupport
    · exact ((f.continuous.comp continuous_snd).mul (hφ.comp hact)).continuousOn
    · intro q a _ ha
      exact mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport ha) _
  have hpt := (Langlands.Analysis.integratedTranslationPointwise Q ν A μG act hact.measurable
    hpres (haarQuotientL2BoundedRightAction F G T i hi I e hc)
    (norm_haarQuotientL2BoundedRightAction F G T i hi I e hc)
    (haarQuotientL2Orbit_aestronglyMeasurable F G T i hi I e hc μG)
    (coeFn_quotientL2RightTranslate F G T i ν hpres) f hf (hm.toLp φ)).2
  have hrep : (R (hm.toLp φ) : Q → ℂ) =ᵐ[ν] ψ := by
    have hcomp₁ := (Lp.stronglyMeasurable (hm.toLp φ)).comp_measurable hact.measurable
    have hcomp₂ := hφ.stronglyMeasurable.comp_measurable hact.measurable
    have hcomp : ∀ᵐ q ∂ν, ∀ᵐ a ∂μG, hm.toLp φ (act q a) = φ (act q a) :=
      (Measure.ae_ae_comm (hcomp₁.measurableSet_eq_fun hcomp₂)).mpr
        (Filter.Eventually.of_forall fun a => (hpres a).quasiMeasurePreserving.ae_eq_comp hm.coeFn_toLp)
    filter_upwards [hpt, hcomp] with q hq hq'
    change ∀ᵐ a ∂μG, hm.toLp φ (act q a) = φ (act q a) at hq'
    calc R (hm.toLp φ) q = ∫ a, f a * hm.toLp φ (act q a) ∂μG := hq
      _ = ψ q := integral_congr_ae (hq'.mono fun a ha => congrArg (fun z => f a * z) ha)
  change (R (hm.toLp φ) : Q → ℂ) ∈ aeParabolicCuspidalFunctionSubmodule F G hPD hG T i
  rw [mem_aeParabolicCuspidalFunctionSubmodule_congr F G hPD hG T i hi I e hc _ ψ
    (Lp.stronglyMeasurable _) hψ.stronglyMeasurable hrep]
  intro P
  let U := properRationalParabolicRadicals hPD hG P
  let N := AdelicSubgroupPoints.adelicPoints F G U
  let Λ := AdelicSubgroupPoints.rationalSubgroup F G U
  let dn := properParabolicHaarMeasure F G hPD hG P
  have hΛ := AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G U
  let : (Measure.haar : Measure N).IsMulRightInvariant :=
    AdelicSubgroupPoints.haar_isMulRightInvariant_of_compactRationalQuotient F G U
  let : dn.IsHaarMeasure := by
    change (AdelicSubgroupPoints.quotientMassNormalizer F G U • (Measure.haar : Measure N)).IsHaarMeasure
    exact Measure.IsHaarMeasure.smul _ (AdelicSubgroupPoints.quotientMassNormalizer_ne_zero F G U)
      (AdelicSubgroupPoints.quotientMassNormalizer_ne_top F G U)
  let : dn.IsMulRightInvariant := by
    change (AdelicSubgroupPoints.quotientMassNormalizer F G U • (Measure.haar : Measure N)).IsMulRightInvariant
    infer_instance
  let : dn.IsInvInvariant := ConstantTermAverage.isInvInvariant_of_isMulRightInvariant dn
  -- The ambient radical measure and its quotient use the same normalizing factor.
  have hνP : properParabolicQuotientMeasure F G hPD hG P =
      LeftCosetSpace.discreteQuotientMeasure Λ hΛ dn := by
    change AdelicSubgroupPoints.quotientMassNormalizer F G U •
        LeftCosetSpace.quotientMeasure Λ Measure.haar (LeftCosetSpace.fundamentalDomain Λ hΛ) =
      LeftCosetSpace.quotientMeasure Λ dn (LeftCosetSpace.fundamentalDomain Λ hΛ)
    symm
    exact LeftCosetSpace.quotientMeasure_smul Λ _ _ _
  let Φ (b : A) := φ (LeftCosetSpace.mk Γ b)
  have hΦ := hφ.comp (LeftCosetSpace.continuous_mk Γ)
  have hΦinv (δ : Λ) (b : A) : Φ (((δ : N) : A) * b) = Φ b := by
    have hδ : ((δ : N) : A) ∈ rationalSubgroup F G := by
      obtain ⟨r, hr⟩ := δ.2
      exact ⟨r.val, congrArg Subtype.val hr⟩
    exact congrArg φ (LeftCosetSpace.mk_subgroup_mul Γ
      ⟨_, rationalSubgroup_le_positiveRationalSubgroup F G T i hδ⟩ b)
  have hperiod (g : normOneSubgroup F G) :
      HasConvergentProperParabolicPositivePeriod F G hPD hG T i P ψ g ∧
        properParabolicPositivePeriod F G hPD hG T i P ψ g = 0 := by
    unfold HasConvergentProperParabolicPositivePeriod properParabolicPositivePeriod
    rw [hνP]
    exact convolutionPeriod_zero μG N (isClosed_properRationalParabolicRadicalAdelicPoints F G hPD hG P)
      Λ hΛ dn f (hvanish P) Φ hΦ hΦinv (g : A)
      (properParabolicPositivePeriodIntegrand F G hPD hG T i P ψ g)
      (fun n => properParabolicPositivePeriodIntegrand_mk F G hPD hG T i P ψ g n)
  exact ⟨Filter.Eventually.of_forall (fun g => (hperiod g).1),
    Filter.Eventually.of_forall (fun g => (hperiod g).2)⟩

end Langlands.TraceFormula
