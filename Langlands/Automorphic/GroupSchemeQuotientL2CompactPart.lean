import Langlands.Automorphic.GroupSchemeQuotientL2ContinuousRepresentativeProof
import Langlands.Analysis.HilbertSchmidtCompactProof
import Langlands.Analysis.HilbertSchmidtEvaluationProof
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! # Convolution on a compact part of the actual positive rational quotient -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Filter Topology Set
open scoped CategoryTheory.MonObj CompactlySupported
open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme Langlands.QuotientIntegration Langlands.Analysis.OperatorIdeals

namespace Langlands.Automorphic.GroupSchemeFunctions

section Cutoff

variable {X : Type v} [MeasurableSpace X] {ν : Measure X} {D : Set X} (hD : MeasurableSet D)

/-- Multiplication by the indicator of a measurable set on the same `L²` space. -/
def quotientL2Indicator : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν := by
  let F (x : Lp ℂ 2 ν) := ((Lp.memLp x).indicator hD.nullMeasurableSet).toLp (D.indicator x)
  have hF (x : Lp ℂ 2 ν) : (F x : X → ℂ) =ᵐ[ν] D.indicator x := MemLp.coeFn_toLp _
  let L : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := F
      map_add' x y := by
        apply Lp.ext
        filter_upwards [hF (x + y), hF x, hF y, Lp.coeFn_add x y, Lp.coeFn_add (F x) (F y)]
          with q hxy hx hy hadd hfadd
        by_cases hq : q ∈ D <;> simp only [hxy, hx, hy, hadd, hfadd,
          Pi.add_apply, indicator_of_mem, indicator_of_notMem, hq, not_false_eq_true, zero_add]
      map_smul' r x := by
        apply Lp.ext
        filter_upwards [hF (r • x), hF x, Lp.coeFn_smul r x, Lp.coeFn_smul r (F x)] with q hrx hx hs hfs
        by_cases hq : q ∈ D <;> simp only [hrx, hx, hs, hfs, Pi.smul_apply, RingHom.id_apply,
          indicator_of_mem, indicator_of_notMem, hq, not_false_eq_true, smul_zero] }
  refine L.mkContinuous 1 fun x => ?_
  rw [one_mul]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hF x] with q hx
  change ‖F x q‖ ≤ ‖x q‖
  rw [hx]
  by_cases hq : q ∈ D
  · rw [indicator_of_mem hq]
  · rw [indicator_of_notMem hq, norm_zero]
    exact norm_nonneg _

theorem quotientL2Indicator_ae (x : Lp ℂ 2 ν) :
    (quotientL2Indicator hD x : X → ℂ) =ᵐ[ν] D.indicator x :=
  MemLp.coeFn_toLp ((Lp.memLp x).indicator hD.nullMeasurableSet)

end Cutoff

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

local notation "A" => AdelicGroupPoints F G
local notation "Q" => PositiveRationalQuotient F G T i
local notation "Γ" => positiveRationalSubgroup F G T i
local notation "mQ" => positiveRationalQuotientHaarMeasure F G T i
local notation "mG" => (Measure.haar : Measure A)
local notation "R" => haarQuotientL2IntegratedAction F G T i hi I e hc mG
local notation "E" => Lp ℂ 2 mQ

omit [LocallyOfFiniteType G.X.hom] [(characterRestrict i).range.FiniteIndex]
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant] in
/-- Joint continuity of actual right translation on the positive rational quotient. -/
theorem continuous_positiveQuotient_rightTranslate :
    Continuous (fun p : Q × A => LeftCosetSpace.rightTranslate Γ p.2 p.1) := by
  let hq := LeftCosetSpace.isOpenQuotientMap_mk Γ
  rw [(hq.prodMap IsOpenQuotientMap.id).isQuotientMap.continuous_iff]
  exact hq.continuous.comp (continuous_fst.mul continuous_snd)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 850000 in
/-- The compact convolution kernel descends to one continuous family of `L²` rows on the
actual positive rational quotient. Each row gives the absolutely convergent integral
at every representative and the original integrated action almost everywhere. -/
theorem exists_positiveQuotientL2ConvolutionRows (f : C_c(A, ℂ)) (hf : Integrable f mG) :
    ∃ k : Q → E, Continuous k ∧
      (∀ (x : A) (φ : E), Integrable (fun a => f a * φ (LeftCosetSpace.mk Γ (x * a))) mG ∧
        inner ℂ (k (LeftCosetSpace.mk Γ x)) φ =
          ∫ a, f a * φ (LeftCosetSpace.mk Γ (x * a)) ∂mG) ∧
      ∀ φ : E, (R f hf φ : Q → ℂ) =ᵐ[mQ] fun q => inner ℂ (k q) φ := by
  let : BorelSpace Q := positiveRationalQuotient_borelSpace F G T i hi I e hc
  let : T2Space Q := positiveRationalQuotient_t2Space F G T i hi I e hc
  let : IsLocallyFiniteMeasure mQ := positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure F G T i hi I e hc
  let : SecondCountableTopology Q :=
    TopologicalSpace.Quotient.secondCountableTopology (LeftCosetSpace.isOpenQuotientMap_mk Γ).isOpenMap
  let μH := positiveRationalSubgroupHaarMeasure F G T i hi I e hc
  let : μH.IsHaarMeasure := positiveRationalSubgroupHaarMeasure_isHaarMeasure F G T i hi I e hc
  let : SigmaFinite μH := positiveRationalSubgroupHaarMeasure_sigmaFinite F G T i hi I e hc
  let : μH.IsMulRightInvariant := positiveRationalSubgroupHaarMeasure_isMulRightInvariant F G T i hi I e hc
  obtain ⟨k₀, hkc, hk, _⟩ := quotientConvolutionKernel Γ
    (isClosed_positiveRationalSubgroup F G T i hi I e hc) μH mG mQ
    (positiveRationalQuotientHaarMeasure_isCompatible F G T i hi I e hc) f
  have hinv (b : Γ) (x : A) : k₀ (b.val * x) = k₀ x := by
    apply ext_inner_right ℂ
    intro φ
    rw [(hk _ φ).2, (hk x φ).2]
    apply integral_congr_ae (Eventually.of_forall fun a => ?_)
    change f a * φ (LeftCosetSpace.mk Γ ((b.val * x) * a)) = f a * φ (LeftCosetSpace.mk Γ (x * a))
    rw [mul_assoc, LeftCosetSpace.mk_subgroup_mul Γ b]
  let k := LeftCosetSpace.lift Γ k₀ hinv
  refine ⟨k, LeftCosetSpace.continuous_lift Γ k₀ hinv hkc, ?_, ?_⟩
  · intro x v
    exact hk x v
  · intro φ
    let act (q : Q) (a : A) := LeftCosetSpace.rightTranslate Γ a q
    let hR := haarQuotientMeasureRightInvariant F G T i hi I e hc
    have hc' := continuous_positiveQuotient_rightTranslate F G T i
    have hmeas : Measurable (Function.uncurry act) := hc'.measurable
    have hpt := (Langlands.Analysis.integratedTranslationPointwise Q mQ A mG act hmeas hR
      (haarQuotientL2BoundedRightAction F G T i hi I e hc)
      (norm_haarQuotientL2BoundedRightAction F G T i hi I e hc)
      (haarQuotientL2Orbit_aestronglyMeasurable F G T i hi I e hc mG)
      (coeFn_quotientL2RightTranslate F G T i mQ hR) f hf φ).2
    filter_upwards [hpt] with q hq
    obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective Γ q
    exact hq.trans (hk x φ).2.symm

set_option maxHeartbeats 700000 in
/-- Multiplication of an integrated quotient convolution by the indicator of a compact
set is Hilbert–Schmidt, using the continuous kernel rows on that set. -/
theorem isCompactOperator_positiveQuotientL2CompactPart (f : C_c(A, ℂ)) (hf : Integrable f mG)
    (D : Set Q) (hD : IsCompact D) (hm : MeasurableSet D) :
    IsCompactOperator (quotientL2Indicator hm ∘L R f hf) := by
  classical
  let : IsLocallyFiniteMeasure mQ :=
    positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure F G T i hi I e hc
  obtain ⟨k, hkc, _, hk⟩ := exists_positiveQuotientL2ConvolutionRows F G T i hi I e hc f hf
  obtain ⟨C, hC⟩ := hD.exists_bound_of_continuousOn hkc.continuousOn
  let kD (q : Q) : E →L[ℂ] ℂ := if q ∈ D then innerSL ℂ (k q) else 0
  let w := D.indicator (fun _ => (max C 0) ^ 2)
  have hw : Integrable w mQ := (integrableOn_const hD.measure_lt_top.ne).integrable_indicator hm
  have hrep (φ : E) : ((quotientL2Indicator hm ∘L R f hf) φ : Q → ℂ) =ᵐ[mQ] fun q => kD q φ := by
    filter_upwards [quotientL2Indicator_ae hm (R f hf φ), hk φ] with q hq hφ
    change quotientL2Indicator hm (R f hf φ) q = kD q φ
    rw [hq]
    by_cases hqD : q ∈ D
    · rw [indicator_of_mem hqD, hφ]
      simp only [kD, ite_eq_left hqD, innerSL_apply_apply]
    · rw [indicator_of_notMem hqD]
      simp only [kD, ite_eq_right hqD, zero_apply]
  have hbound : ∀ᵐ q ∂mQ, ‖kD q‖ ^ 2 ≤ w q := Eventually.of_forall fun q => by
    by_cases hq : q ∈ D
    · simp only [kD, ite_eq_left hq, innerSL_apply_norm, w, indicator_of_mem hq]
      exact pow_le_pow_left₀ (norm_nonneg _) ((hC q hq).trans (le_max_left _ _)) 2
    · simp only [kD, ite_eq_right hq, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, w, indicator_of_notMem hq, le_refl]
  exact hilbertSchmidtCompact E E _
    (hilbertSchmidtDominatedEvaluation.{u, u, u} E Q mQ _ kD w hw hrep hbound).1

end Langlands.Automorphic.GroupSchemeFunctions
