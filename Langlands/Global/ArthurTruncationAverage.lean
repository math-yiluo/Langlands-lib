import Langlands.Global.ArthurTruncation
import Langlands.Global.AdelicConstantTermAverage
import Langlands.Global.AdelicConstantTermComposition
import Langlands.Analysis.Local.QuotientTopology

/-! # Measurable averages along a compact radical quotient -/

noncomputable section

set_option linter.unusedSectionVars false

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj Pointwise ENNReal

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme AdelicSubgroupPoints LeftCosetSpace

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (U : SubgroupFunctor G)

local notation "A" => AdelicGroupPoints F G
local notation "N" => adelicPoints F G U
local notation "Δ" => AdelicSubgroupPoints.rationalSubgroup F G U
local notation "Q" => AdelicSubgroupPoints.RationalQuotient F G U

variable [hclosed : IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G))]
  [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G U)]

local instance radicalLocallyCompactSpace : LocallyCompactSpace N := hclosed.locallyCompactSpace
local instance radicalQuotientBorelSpace : BorelSpace Q := rationalQuotientBorelSpace F G U

local notation "μU" => normalizedRationalQuotientHaarMeasure F G U

local instance radicalQuotientProbability : IsProbabilityMeasure μU :=
  normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G U

/-- Compactness of the radical quotient gives a compact family of representatives. -/
theorem exists_compact_radical_representatives :
    ∃ E : Set N, IsCompact E ∧ ∀ q : Q, ∃ n ∈ E, mk Δ n = q := by
  obtain ⟨E, hE, he⟩ := Langlands.QuotientIntegration.leftQuotient_exists_isCompact_image
    Δ (Subgroup.isClosed_of_isDiscrete Δ (isDiscrete_rationalSubgroup F G U)) isCompact_univ
  refine ⟨E, hE, fun q => ?_⟩
  have hq : q ∈ _ := he.symm ▸ Set.mem_univ q
  exact hq

variable {Λ : Subgroup (AdelicGroupPoints F G)}
  (hUΛ : ∀ n ∈ AdelicSubgroupPoints.rationalSubgroup F G U,
    ((n : adelicPoints F G U) : AdelicGroupPoints F G) ∈ Λ)

local notation "qN" => mk Δ
local notation "qΛ" => mk Λ
private def fibre (z : A × Q) : LeftCosetSpace Λ :=
  subgroupFiberEval Λ Δ (Subgroup.subtype N) (fun _ hn => hUΛ _ hn) id z.1 z.2

private theorem fibre_apply (x : A) (q : Q) :
    fibre U hUΛ (x, q) = qΛ (((q.out : N) : A) * x) := by
  conv_lhs => rw [← Quotient.out_eq q]
  rfl

private theorem continuous_fibre : Continuous (fibre U hUΛ) :=
  continuous_subgroupFiberEval Λ Δ (Subgroup.subtype N) (fun _ hn => hUΛ _ hn)
    continuous_subtype_val continuous_id

private theorem out_eq_of_mk {f : A → ℂ} (hf : ∀ l ∈ Λ, ∀ x, f (l * x) = f x) (x : A) :
    f (qΛ x).out = f x := by
  obtain ⟨l, hl⟩ := RankinSelbergGlobal.Unfolding.exists_out_mk_eq Λ x
  rw [hl, hf _ l.property]

private theorem measurable_descended {f : A → ℂ} (hf : Measurable f)
    (hinv : ∀ l ∈ Λ, ∀ x, f (l * x) = f x) :
    Measurable (fun y : LeftCosetSpace Λ => f y.out) := by
  apply measurable_from_quotient.mpr
  change Measurable ((fun y : LeftCosetSpace Λ => f y.out) ∘ qΛ)
  rw [show (fun y : LeftCosetSpace Λ => f y.out) ∘ qΛ = f from funext (out_eq_of_mk hinv)]
  exact hf

include hUΛ in
private theorem measurable_radical_integrand (hΛ : IsDiscrete (Λ : Set A))
    {f : A → ℂ} (hf : Measurable f) (hinv : ∀ l ∈ Λ, ∀ x, f (l * x) = f x) :
    Measurable (fun z : A × Q => f (((z.2.out : N) : A) * z.1)) := by
  let : BorelSpace (LeftCosetSpace Λ) := discreteQuotientBorelSpace Λ hΛ
  have h := (measurable_descended hf hinv).comp (continuous_fibre U hUΛ).measurable
  convert h using 1
  funext z
  exact ((congrArg (fun y : LeftCosetSpace Λ => f y.out) (fibre_apply U hUΛ z.1 z.2)).trans
    (out_eq_of_mk hinv _)).symm

include hUΛ in
private theorem radical_integrand_bound {f : A → ℂ}
    (hf : IsLocallyBoundedInvariant Λ f) {C : Set A} (hC : IsCompact C) :
    ∃ M : ℝ, ∀ x ∈ C, ∀ q : Q, ‖f (((q.out : N) : A) * x)‖ ≤ M := by
  obtain ⟨E, hE, he⟩ := exists_compact_radical_representatives U
  obtain ⟨M, hM⟩ := hf.2.1 ((fun n : N => (n : A)) '' E * C)
    ((hE.image continuous_subtype_val).mul hC)
  refine ⟨M, fun x hx q => ?_⟩
  obtain ⟨n, hn, hq⟩ := he q
  have hrel : (q.out : N) * n⁻¹ ∈ Δ := (mk_eq_mk_iff Δ n q.out).mp (hq.trans (Quotient.out_eq q).symm)
  have heq : ((q.out : N) : A) * x = ((((q.out : N) * n⁻¹ : N) : A) * ((n : A) * x)) := by
    change (q.out : N).val * x = ((q.out : N).val * (n : A)⁻¹) * ((n : A) * x)
    group
  rw [heq, hf.2.2 _ (hUΛ _ hrel)]
  exact hM _ (Set.mul_mem_mul ⟨n, hn, rfl⟩ hx)

include hUΛ in
/-- A locally bounded invariant measurable function has absolutely convergent radical integrals. -/
theorem integrable_radical_integrand (hΛ : IsDiscrete (Λ : Set A))
    {f : A → ℂ} (hf : IsLocallyBoundedInvariant Λ f) (x : A) :
    Integrable (fun q : Q => f (((q.out : N) : A) * x)) μU := by
  obtain ⟨M, hM⟩ := radical_integrand_bound U hUΛ hf (isCompact_singleton (x := x))
  exact (integrable_const M).mono'
    ((measurable_radical_integrand U hUΛ hΛ hf.1 hf.2.2).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall (hM x (Set.mem_singleton x)))

include hUΛ in
/-- Measurability and boundedness on compact sets are preserved by the normalized radical average. -/
theorem compactAverage_locallyBounded (hΛ : IsDiscrete (Λ : Set A))
    {f : A → ℂ} (hf : IsLocallyBoundedInvariant Λ f) :
    Measurable (ConstantTermComposition.average U f) ∧
      ∀ C : Set A, IsCompact C → ∃ M : ℝ, ∀ x ∈ C, ‖ConstantTermComposition.average U f x‖ ≤ M := by
  have hm := (measurable_radical_integrand U hUΛ hΛ hf.1 hf.2.2).stronglyMeasurable
  refine ⟨hm.integral_prod_right'.measurable, fun C hC => ?_⟩
  obtain ⟨M, hM⟩ := radical_integrand_bound U hUΛ hf hC
  refine ⟨M, fun x hx => ?_⟩
  unfold ConstantTermComposition.average
  calc
    ‖∫ q : Q, f (((q.out : N) : A) * x) ∂μU‖ ≤
        ∫ q : Q, ‖f (((q.out : N) : A) * x)‖ ∂μU := norm_integral_le_integral_norm _
    _ ≤ ∫ _ : Q, M ∂μU := integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) (integrable_const _)
        (Filter.Eventually.of_forall (hM x hx))
    _ = M := by simp [measureReal_def]

variable (hΓ : ∀ l ∈ Λ, ∀ n ∈ AdelicSubgroupPoints.rationalSubgroup F G U,
  ∃ n' ∈ AdelicSubgroupPoints.rationalSubgroup F G U,
    ((n' : adelicPoints F G U) : AdelicGroupPoints F G) = l * n * l⁻¹)
  (hnorm : ∀ l ∈ Λ, ∀ n ∈ adelicPoints F G U, l * n * l⁻¹ ∈ adelicPoints F G U)

include hUΛ hΓ hnorm in
/-- Conjugation preserving the rational radical lattice preserves its quotient probability,
so the radical average descends through the rational parabolic. -/
theorem compactAverage_mul_left {f : A → ℂ} (hinv : ∀ l ∈ Λ, ∀ x, f (l * x) = f x)
    (l : Λ) (x : A) :
    ConstantTermComposition.average U f ((l : A) * x) = ConstantTermComposition.average U f x := by
  let e := ConstantTermAverage.conjEquiv F G U Λ hnorm l⁻¹
  have he (n : N) : e n ∈ Δ ↔ n ∈ Δ :=
    (ConstantTermAverage.mem_rationalSubgroup_conjEquiv_iff F G U Λ ⟨hUΛ, hΓ⟩ hnorm l⁻¹ n).symm
  let a := Langlands.QuotientIntegration.quotientAutomorphism Δ e he
  have ha : MeasurePreserving a μU μU := measurePreserving_rationalQuotientAutomorphism F G U e he
  have h (q : Q) : f (((q.out : N) : A) * ((l : A) * x)) = f ((((a q).out : N) : A) * x) := by
    have heq : fibre U hUΛ ((l : A) * x, q) = fibre U hUΛ (x, a q) := by
      obtain ⟨n, rfl⟩ := mk_surjective Δ q
      change qΛ ((n : A) * ((l : A) * x)) = qΛ ((e n : A) * x)
      have hc : (e n : A) * x = (l : A)⁻¹ * ((n : A) * ((l : A) * x)) := by
        change ((l : A)⁻¹ * (n : A) * ((l : A)⁻¹)⁻¹) * x = _
        group
      rw [hc]
      exact (mk_subgroup_mul Λ l⁻¹ _).symm
    rw [fibre_apply U hUΛ, fibre_apply U hUΛ] at heq
    rw [← out_eq_of_mk hinv (((q.out : N) : A) * ((l : A) * x)),
      ← out_eq_of_mk hinv ((((a q).out : N) : A) * x), heq]
  unfold ConstantTermComposition.average
  rw [integral_congr_ae (Filter.Eventually.of_forall h)]
  exact ha.integral_comp a.measurableEmbedding (fun q : Q => f (((q.out : N) : A) * x))

section Integral

variable (hΛ : IsDiscrete (Λ : Set (AdelicGroupPoints F G)))

local notation "dΛ" => fundamentalDomain Λ hΛ
local notation "haarA" => (Measure.haar : Measure A)
local notation "μΛ" => quotientMeasure Λ haarA dΛ

include hΓ hnorm in
private theorem map_fibre : Measure.map (fibre U hUΛ) ((Measure.restrict haarA dΛ).prod μU) = μΛ := by
  let : BorelSpace (LeftCosetSpace Λ) := discreteQuotientBorelSpace Λ hΛ
  have hfm := (continuous_fibre U hUΛ).measurable
  ext S hS
  let χ : A → ℝ≥0∞ := fun x => S.indicator 1 (qΛ x)
  have hm : Measurable χ := (measurable_one.indicator hS).comp (measurable_mk Λ)
  have hinv (l : Λ) (x : A) : χ ((l : A) * x) = χ x := by
    change S.indicator 1 (qΛ ((l : A) * x)) = S.indicator 1 (qΛ x)
    rw [mk_subgroup_mul]
  rw [Measure.map_apply hfm hS, ← lintegral_indicator_one (hfm hS), quotientMeasure,
    Measure.map_apply (measurable_mk Λ) hS, ← lintegral_indicator_one (measurable_mk Λ hS)]
  have hchi (z : A × Q) : (fibre U hUΛ ⁻¹' S).indicator (1 : A × Q → ℝ≥0∞) z =
      χ (((z.2.out : N) : A) * z.1) := by
    change (fibre U hUΛ ⁻¹' S).indicator (1 : A × Q → ℝ≥0∞) z =
      S.indicator 1 (qΛ (((z.2.out : N) : A) * z.1))
    rw [← fibre_apply U hUΛ z.1 z.2]
    exact Set.indicator_comp_right (s := S) (fibre U hUΛ)
      (g := (1 : LeftCosetSpace Λ → ℝ≥0∞)) (x := z)
  rw [lintegral_prod _ (measurable_one.indicator (hfm hS)).aemeasurable]
  simp_rw [hchi]
  exact ConstantTermAverage.setLIntegral_lowerConstantTerm F G U Λ ⟨hUΛ, hΓ⟩ hnorm hΛ hm
    (fun l hl x => hinv ⟨l, hl⟩ x)

include hUΛ hΓ hnorm in
/-- Integration of the normalized radical average over a parabolic fundamental domain
preserves the integral of an integrable parabolic-invariant function. -/
theorem setIntegral_compactAverage {f : A → ℂ} (hf : Measurable f)
    (hinv : ∀ l ∈ Λ, ∀ x, f (l * x) = f x) (hint : IntegrableOn f dΛ haarA) :
    (∫ x in dΛ, ConstantTermComposition.average U f x ∂haarA) = ∫ x in dΛ, f x ∂haarA := by
  let : BorelSpace (LeftCosetSpace Λ) := discreteQuotientBorelSpace Λ hΛ
  let fQ := fun y : LeftCosetSpace Λ => f y.out
  have hfQm : Measurable fQ := measurable_descended hf hinv
  have hfQ : Integrable fQ μΛ := (RankinSelbergGlobal.Unfolding.integrable_out_iff Λ hf
    (fun l x => hinv l l.2 x) haarA dΛ).mpr hint
  have hmp : MeasurePreserving (fibre U hUΛ) ((Measure.restrict haarA dΛ).prod μU) μΛ :=
    ⟨(continuous_fibre U hUΛ).measurable, map_fibre U hUΛ hΓ hnorm hΛ⟩
  have hprod := hmp.integrable_comp_of_integrable hfQ
  have hval (x : A) (q : Q) : fQ (fibre U hUΛ (x, q)) = f (((q.out : N) : A) * x) := by
    rw [fibre_apply U hUΛ]
    exact out_eq_of_mk hinv _
  calc
    (∫ x in dΛ, ConstantTermComposition.average U f x ∂haarA) =
        ∫ x in dΛ, ∫ q, (fQ ∘ fibre U hUΛ) (x, q) ∂μU ∂haarA := by
      simp only [Function.comp_apply, hval, ConstantTermComposition.average]
    _ = ∫ z, (fQ ∘ fibre U hUΛ) z ∂((Measure.restrict haarA dΛ).prod μU) :=
      (integral_prod _ hprod).symm
    _ = ∫ y, fQ y ∂μΛ := by
      simp only [Function.comp_apply]
      rw [← integral_map hmp.measurable.aemeasurable hfQm.aestronglyMeasurable, hmp.map_eq]
    _ = ∫ x in dΛ, f x ∂haarA := RankinSelbergGlobal.Unfolding.integral_out_eq Λ hf
      (fun l x => hinv l l.2 x) haarA dΛ

end Integral

end Langlands.Global.ArthurTruncation
