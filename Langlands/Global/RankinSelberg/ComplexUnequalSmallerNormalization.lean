import Langlands.Global.RankinSelberg.ComplexUnequalTranslateContinuity
import Langlands.Global.RankinSelberg.OrdinaryNormalizationLinear

/-! # Translated unequal normalization linear in the smaller coefficient -/

noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Operator NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapRetained

open ArchimedeanLocal Langlands.Archimedean Langlands.Automorphic
open Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open ComplexJacquet (HasComplexPairNormalizedGrowth)
open ComplexUnequalFamily (continuous_ordinaryKernel continuous_dualKernel)
open ComplexUnequalWeightedTranslation (complexUnequalTranslateContinuity hasLeftCharacter_of_rightTranslate
  translatedUnequalDomination)
open ComplexWeightedKernelReflection (pairReflectionFactor)
open FunctionalEquationComparison.CompletedEquationAdapter (complexPairLFactor_denominator_ne_zero)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel
  archimedeanEquationComplexQMeasurable archimedeanEquationComplexQBorel

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "Q" => fun t => LeftUnipotentQuotient t ℂ
local notation "ρ" => ArchimedeanLocal.translateFunction

variable {r t : ℕ}
local notation "H" => G (t + 1)
local notation "X" => Q t × Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℂ
local notation "KF[" es "]" => complexStandardKFinite (t + 1) es

private theorem translate_one (f : H → ℂ) : ρ (1 : H) f = f := by
  funext x
  change f (x * 1) = f x
  rw [mul_one]

private theorem translated_integrable (h : t < r) (a : ℂˣ) (D : ComplexQuotientMeasureData t)
    {ds es : List ComplexCharacterData} (W : complexWhittakerModel r ds a)
    (V : complexWhittakerModel t es (-a)) (g : G (r + 1)) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (complexUnequalIntegrand h (ρ g W.val) V.val s) D.measure ∧
      Integrable (complexUnequalDualKernel h (ρ g W.val) V.val s) (complexUnequalDualMeasure a D) := by
  let w := ρ g W.val
  let v := ρ (1 : H) V.val
  have hw := hasLeftCharacter_of_rightTranslate W g
  have hv := hasLeftCharacter_of_rightTranslate V (1 : H)
  have hwc : Continuous w := (contMDiff_of_mem_complexWhittakerModel W.2).continuous.comp (continuous_id.mul_const g)
  have hvc : Continuous v := (contMDiff_of_mem_complexWhittakerModel V.2).continuous.comp (continuous_id.mul_const (1 : H))
  obtain ⟨b, hb, hbd⟩ := translatedUnequalDomination h a D W V {g} {1} isCompact_singleton isCompact_singleton
  refine ⟨b, fun s hs => ?_⟩
  obtain ⟨B, hB, hBounds⟩ := hb s.re
  obtain ⟨C, hC, hBoundsd⟩ := hbd s.re
  have hm : (g, 1, s) ∈ ({g} : Set (G (r + 1))) ×ˢ (({1} : Set H) ×ˢ univ) := by simp
  have hI : Integrable (complexUnequalIntegrand h w v s) D.measure :=
    hB.mono' (continuous_ordinaryKernel h hw hv hwc hvc s).aestronglyMeasurable
      (ae_of_all _ (hBounds (g, 1, s) hm hs le_rfl))
  have hId : Integrable (complexUnequalDualKernel h w v s) (complexUnequalDualMeasure a D) :=
    hC.mono' (continuous_dualKernel h hw hv hwc hvc s).aestronglyMeasurable
      (ae_of_all _ (hBoundsd (g, 1, s) hm hs le_rfl))
  simpa only [w, v, translate_one] using And.intro hI hId

private def ordinarySmallerKernel (h : t < r) (W : G (r + 1) → ℂ) {es : List ComplexCharacterData}
    (B : KF[es] →ₗ[ℂ] (H → ℂ)) : KF[es] →ₗ[ℂ] (ℂ → Q t → ℂ) where
  toFun v := complexUnequalIntegrand h W (B v)
  map_add' v w := by
    ext s x
    simp only [complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand, map_add, Pi.add_apply]
    ring
  map_smul' c v := by
    ext s x
    simp only [complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand, map_smul,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

private def dualSmallerKernel (h : t < r) (W : G (r + 1) → ℂ) {es : List ComplexCharacterData}
    (B : KF[es] →ₗ[ℂ] (H → ℂ)) : KF[es] →ₗ[ℂ] (ℂ → X → ℂ) where
  toFun v := complexUnequalDualKernel h W (B v)
  map_add' v w := by
    ext s x
    simp only [complexUnequalDualKernel, ArchimedeanLocal.blockKernel, ArchimedeanLocal.dualFunction,
      map_add, Pi.add_apply]
    ring
  map_smul' c v := by
    ext s x
    simp only [complexUnequalDualKernel, ArchimedeanLocal.blockKernel, ArchimedeanLocal.dualFunction,
      map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The lower-rank ordinary normalization, with the larger coefficient right translated, is
linear in the smaller coefficient and continuous in the translation at every spectral point. -/
def ComplexUnequalSmallerNormalizationStatement : Prop :=
  ∀ (h : t < r) (ds es : List ComplexCharacterData), ds.length = r + 1 → es.length = t + 1 →
    ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData t),
      (∀ (W : complexWhittakerModel r ds a) (V : complexWhittakerModel t es (-a)),
        HasComplexPairNormalizedGrowth ds es a (complexCentralSign es ^ r)
          (complexUnequalIntegral h D W.val V.val) (complexUnequalDualIntegral h a D W.val V.val)) →
      ∀ (W : complexWhittakerModel r ds a) (B : KF[es] →ₗ[ℂ] (H → ℂ)),
        IsComplexWhittakerIntertwiner t es (-a) B →
        ∃ A : G (r + 1) → KF[es] →ₗ[ℂ] (ℂ → ℂ),
          (∀ v s, Continuous (fun g => A g v s)) ∧
          ∀ g v, Differentiable ℂ (A g v) ∧ HasStripExponentialGrowth (A g v) ∧
            ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
              let O := complexUnequalIntegrand h (ρ g W.val) (B v) s
              let R := complexUnequalDualKernel h (ρ g W.val) (B v) s
              Integrable O D.measure ∧ Integrable R (complexUnequalDualMeasure a D) ∧
              A g v s = (complexPairLFactor ds es).denominator s * (∫ x, O x ∂D.measure) ∧
              pairReflectionFactor ds es a (complexCentralSign es ^ r) (1 - s) * A g v (1 - s) =
                (complexPairLFactor (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)).denominator s *
                  ∫ x, R x ∂complexUnequalDualMeasure a D

set_option maxHeartbeats 1600000 in
theorem complexUnequalSmallerNormalization : ComplexUnequalSmallerNormalizationStatement (r := r) (t := t) := by
  intro h ds es hds hes a D hGrowth W B hB
  let V (v : KF[es]) : complexWhittakerModel t es (-a) :=
    ⟨B v, Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨v, rfl⟩)⟩
  choose N Nd hN hC using fun v =>
    complexUnequalTranslateContinuity r t h ds es hds hes a D hGrowth W (V v)
  let P (g : G (r + 1)) : G (r + 1) × H := (g, 1)
  let I (g : G (r + 1)) := ordinarySmallerKernel h (ρ g W.val) B
  have hi (g : G (r + 1)) (v : KF[es]) := translated_integrable h a D W (V v) g
  let L := (complexPairLFactor ds es).denominator
  obtain ⟨σ₀, hσ₀⟩ := complexPairLFactor_denominator_ne_zero ds es
  let hOrd (g : G (r + 1)) (v : KF[es]) : OrdinaryIntegralNormalization
      (fun s => ∫ x, I g v s x ∂D.measure) (fun s => (L s)⁻¹) := by
    refine ⟨N v (P g), (hN v (P g)).1.differentiableOn.analyticOnNhd isOpen_univ, ?_⟩
    obtain ⟨b, hb⟩ := (hN v (P g)).2.2.2.2.1
    refine ⟨max b σ₀, fun s hs => ?_⟩
    let J := ∫ x, I g v s x ∂D.measure
    have hNorm : N v (P g) s = L s * J := by
      simpa only [P, Prod.fst, Prod.snd, V, translate_one, L, J, I, ordinarySmallerKernel,
        LinearMap.coe_mk, AddHom.coe_mk, complexUnequalIntegral, ArchimedeanLocal.unequalIntegral,
        complexUnequalIntegrand] using (hb s ((le_max_left _ _).trans_lt hs)).1
    change J = N v (P g) s * (L s)⁻¹
    rw [hNorm, mul_comm (L s), mul_assoc, mul_inv_cancel₀ (hσ₀ _ ((le_max_right _ _).trans_lt hs)), mul_one]
  have hL : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → (L s)⁻¹ ≠ 0 :=
    ⟨σ₀, fun s hs => inv_ne_zero (hσ₀ s hs)⟩
  choose A hA using fun g => ordinaryNormalizationLinear D.measure (I g)
    (fun s => (L s)⁻¹) hL (fun v => by
      obtain ⟨b, hb⟩ := hi g v
      exact ⟨b, fun s hs => (hb s hs).1⟩) (hOrd g)
  have hA' (g : G (r + 1)) (v : KF[es]) : A g v = N v (P g) := hA g v
  refine ⟨A, fun v s => ?_, fun g v => ?_⟩
  · simp_rw [hA']
    exact (hC v s).comp (continuous_id.prodMk continuous_const)
  · rw [hA']
    obtain ⟨ho, hd, hs, hsd, ⟨b, hb⟩, hE⟩ := hN v (P g)
    obtain ⟨c, hc⟩ := hi g v
    refine ⟨ho, hs, max b c, fun s hs => ?_⟩
    obtain ⟨hIo, hIr⟩ := hc s ((le_max_right b c).trans_lt hs)
    obtain ⟨hO, hR⟩ := hb s ((le_max_left b c).trans_lt hs)
    have hR' : pairReflectionFactor ds es a (complexCentralSign es ^ r) (1 - s) * N v (P g) (1 - s) =
        Nd v (P g) s := by simpa only [pairReflectionFactor, sub_sub_cancel] using (hE (1 - s)).symm
    refine ⟨hIo, hIr, ?_, hR'.trans ?_⟩
    · simpa only [P, Prod.fst, Prod.snd, V, translate_one, complexUnequalIntegral,
        ArchimedeanLocal.unequalIntegral, complexUnequalIntegrand] using hO
    · simpa only [P, Prod.fst, Prod.snd, V, translate_one] using hR

/-- The normalized identities extend along every curve in the span of a fixed finite family
of smaller vectors. The coefficients on the reflected side are evaluated at the reflected point. -/
theorem smallerNormalization_finiteFamily (h : t < r) (ds es : List ComplexCharacterData)
    (a : ℂˣ) (D : ComplexQuotientMeasureData t) (W : G (r + 1) → ℂ)
    (B : KF[es] →ₗ[ℂ] (H → ℂ)) (A : KF[es] →ₗ[ℂ] (ℂ → ℂ))
    {J : Type*} [Fintype J] (v : J → KF[es]) (β : J → ℂ → ℂ)
    (hA : ∀ j, ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      let O := complexUnequalIntegrand h W (B (v j)) s
      let R := complexUnequalDualKernel h W (B (v j)) s
      Integrable O D.measure ∧ Integrable R (complexUnequalDualMeasure a D) ∧
      A (v j) s = (complexPairLFactor ds es).denominator s * (∫ x, O x ∂D.measure) ∧
      pairReflectionFactor ds es a (complexCentralSign es ^ r) (1 - s) * A (v j) (1 - s) =
        (complexPairLFactor (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)).denominator s *
          ∫ x, R x ∂complexUnequalDualMeasure a D) :
    let F (s : ℂ) := ∑ j, β j s • v j
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      A (F s) s = (complexPairLFactor ds es).denominator s * complexUnequalIntegral h D W (B (F s)) s ∧
      pairReflectionFactor ds es a (complexCentralSign es ^ r) (1 - s) * A (F (1 - s)) (1 - s) =
        (complexPairLFactor (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)).denominator s *
          ∫ x, complexUnequalDualKernel h W (B (F (1 - s))) s x ∂complexUnequalDualMeasure a D := by
  intro F
  classical
  choose b hb using hA
  obtain ⟨σ, hσ⟩ := (finite_range b).bddAbove
  refine ⟨σ, fun s hs => ?_⟩
  have hj (j : J) := hb j s ((hσ (mem_range_self j)).trans_lt hs)
  let O := ordinarySmallerKernel h W B
  let R := dualSmallerKernel h W B
  have key {Z : Type} [MeasurableSpace Z] (μ : Measure Z) (K : KF[es] →ₗ[ℂ] (ℂ → Z → ℂ))
      (u : ℂ) (L E : ℂ) (hi : ∀ j, Integrable (K (v j) s) μ)
      (he : ∀ j, E * A (v j) u = L * ∫ x, K (v j) s x ∂μ) :
      E * A (F u) u = L * ∫ x, K (F u) s x ∂μ := by
    simp only [F, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hInt : ∀ j ∈ (Finset.univ : Finset J), Integrable (fun x => β j u * K (v j) s x) μ :=
      fun j _ => (hi j).const_mul _
    rw [integral_finsetSum _ hInt, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, ← mul_assoc E, mul_comm E, mul_assoc, he j]
    ring
  constructor
  · simpa only [O, ordinarySmallerKernel, LinearMap.coe_mk, AddHom.coe_mk, one_mul,
      complexUnequalIntegral, ArchimedeanLocal.unequalIntegral, complexUnequalIntegrand] using
      key D.measure O s ((complexPairLFactor ds es).denominator s) 1 (fun j => (hj j).1) (fun j => by rw [one_mul]; exact (hj j).2.2.1)
  · exact key (complexUnequalDualMeasure a D) R (1 - s)
      ((complexPairLFactor (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)).denominator s)
      (pairReflectionFactor ds es a (complexCentralSign es ^ r) (1 - s))
      (fun j => (hj j).2.1) (fun j => (hj j).2.2.2)

end Langlands.Global.RankinSelbergGlobal.ComplexGapRetained
