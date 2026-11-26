import Langlands.Global.RankinSelberg.ComplexUnequalWeightedTranslation
import Langlands.Global.RankinSelberg.ComplexThetaNormalizedGrowth
import Langlands.Global.RankinSelberg.ComplexUnequalDualFamily
import Langlands.Global.RankinSelberg.ComplexJacquetMultiplicityOne

/-! # Normalized strip growth for translated unequal complex Whittaker pairs -/

noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexUnequalWeightedTranslation

open ArchimedeanLocal Langlands.Archimedean Langlands.Automorphic Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure rectangularMeasure_isAddHaar)
open ArchimedeanMellinPair (theta)
open ArchimedeanRealPairIdentity (norm_kernel)
open ComplexCompactProfileFamily (characterList)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ComplexJacquet (HasComplexPairNormalizedGrowth complexCentralSign_sq)
open ComplexJacquetContinuation (continuedJacquet complexJacquetIntertwiner)
open ComplexJacquetMultiplicityOne (complexJacquetMultiplicityOne exists_characterList)
open ComplexThetaNormalizedGrowth (complexThetaNormalizedGrowth)
open ComplexUnequalFamily (HasLeftCharacter HalfPlaneDomination ordinary_halfPlaneDomination
  dual_halfPlaneDomination continuous_ordinaryKernel continuous_dualKernel)
open ComplexUnequalMellinReduction (quotientDetAbs quotientDetAbs_pos continuous_quotientDetAbs sigmaFinite_quotient
  complexUnequalIntegrand_eq_mul complexUnequalDualKernel_eq_mul)
open ComplexWeightedKernelReflection (ordinaryWeight reflectedWeight complexWeights_data)
open ComplexWhittakerTranslatedIntegrals (weightedOrdinary weightedDual)
open ComplexWhittakerTranslatedMellin (compact_rightTranslate_uniformSimpleRootBound)

attribute [local instance] archimedeanEquationComplexGLMeasurable archimedeanEquationComplexGLBorel
  archimedeanEquationComplexNMeasurable archimedeanEquationComplexNBorel
  archimedeanEquationComplexQMeasurable archimedeanEquationComplexQBorel

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "Q" => fun t => LeftUnipotentQuotient t ℂ
local notation "ρ" => ArchimedeanLocal.translateFunction

/-- The canonical Whittaker map realizes each vector of the model with the specified list. -/
theorem exists_whittakerIntertwiner_value (r : ℕ) (ds : List ComplexCharacterData) (hds : ds.length = r + 1)
    (a : ℂˣ) (W : complexWhittakerModel r ds a) :
    ∃ (B : complexStandardKFinite (r + 1) ds →ₗ[ℂ] (G (r + 1) → ℂ)),
      IsComplexWhittakerIntertwiner r ds a B ∧ ∃ v, B v = W.val := by
  obtain ⟨l, p, rfl⟩ := exists_characterList ds hds
  let μ := complexSelfDualMeasure (-a)
  let B := continuedJacquet μ (-a) l p
  have hB : IsComplexWhittakerIntertwiner r (characterList l p) a B := by
    simpa only [neg_neg] using complexJacquetIntertwiner r μ (-a) l p
  have hR : complexWhittakerModel r (characterList l p) a = B.range := by
    simpa only [neg_neg] using (complexJacquetMultiplicityOne r μ (-a) l p).2
  exact ⟨B, hB, (congrArg (fun M : Submodule ℂ (G (r + 1) → ℂ) => W.val ∈ M) hR).mp W.2⟩

theorem hasLeftCharacter_of_rightTranslate {r : ℕ} {ds : List ComplexCharacterData} {a : ℂˣ}
    (W : complexWhittakerModel r ds a) (g : G (r + 1)) : HasLeftCharacter a (ρ g W.val) := by
  intro u x
  change W.val ((u.val * x) * g) = _
  rw [mul_assoc, complexWhittakerModel_left_equivariant W.2 _ u.2]
  rfl

/-- Compact sets of translation parameters have a common right-half-plane bound, on each
bounded interval of real parts, for both ordinary and reflected unequal-rank kernels. -/
theorem translatedUnequalDomination {r t : ℕ} (h : t < r) (a : ℂˣ) (D : ComplexQuotientMeasureData t)
    {ds es : List ComplexCharacterData} (W : complexWhittakerModel r ds a) (V : complexWhittakerModel t es (-a))
    (S : Set (G (r + 1))) (T : Set (G (t + 1))) (hS : IsCompact S) (hT : IsCompact T) :
    let A (p : G (r + 1) × G (t + 1) × ℂ) := ρ p.1 W.val
    let C (p : G (r + 1) × G (t + 1) × ℂ) := ρ p.2.1 V.val
    let U := S ×ˢ (T ×ˢ (univ : Set ℂ))
    ∃ σ : ℝ,
      HalfPlaneDomination D.measure U (fun p => p.2.2) (fun p => complexUnequalIntegrand h (A p) (C p) p.2.2) σ ∧
      HalfPlaneDomination (complexUnequalDualMeasure (r := r) a D) U (fun p => p.2.2)
        (fun p => complexUnequalDualKernel h (A p) (C p) p.2.2) σ := by
  intro A C U
  obtain ⟨M, hM⟩ := compact_rightTranslate_uniformSimpleRootBound W S hS
  obtain ⟨N, hN⟩ := compact_rightTranslate_uniformSimpleRootBound V T hT
  have hMb : HasUniformSimpleRootBound U A := by
    refine ⟨M, fun j => ?_⟩
    obtain ⟨B, hB, hb⟩ := hM j
    exact ⟨B, hB, fun p hp x => hb p.1 hp.1 x⟩
  have hNb : HasUniformSimpleRootBound U C := by
    refine ⟨N, fun j => ?_⟩
    obtain ⟨B, hB, hb⟩ := hN j
    exact ⟨B, hB, fun p hp x => hb p.2.1 hp.2.1 x⟩
  have hA (p : G (r + 1) × G (t + 1) × ℂ) : HasLeftCharacter a (A p) :=
    hasLeftCharacter_of_rightTranslate W p.1
  have hC (p : G (r + 1) × G (t + 1) × ℂ) : HasLeftCharacter (-a) (C p) :=
    hasLeftCharacter_of_rightTranslate V p.2.1
  obtain ⟨b, hb⟩ := ordinary_halfPlaneDomination h D U A C (fun p => p.2.2) hA hC hMb hNb
  obtain ⟨bd, hbd⟩ := dual_halfPlaneDomination h a D U A C (fun p => p.2.2) hA hC hMb hNb
  refine ⟨max b bd, ?_, ?_⟩
  · intro τ
    obtain ⟨B, hB, h⟩ := hb τ
    exact ⟨B, hB, fun p hp hs ht x => h p hp ((le_max_left b bd).trans_lt hs) ht x⟩
  · intro τ
    obtain ⟨B, hB, h⟩ := hbd τ
    exact ⟨B, hB, fun p hp hs ht x => h p hp ((le_max_right b bd).trans_lt hs) ht x⟩

/-- The ordinary and reflected product integrals for any two fixed right translates of a
complex Whittaker pair have the same normalized reflection and strip growth as model vectors. -/
def ComplexUnequalTranslateGrowthStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (ds es : List ComplexCharacterData), ds.length = r + 1 → es.length = t + 1 →
    ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData t),
      (∀ (W : complexWhittakerModel r ds a) (V : complexWhittakerModel t es (-a)),
        HasComplexPairNormalizedGrowth ds es a (complexCentralSign es ^ r)
          (complexUnequalIntegral h D W.val V.val) (complexUnequalDualIntegral h a D W.val V.val)) →
      ∀ (W : complexWhittakerModel r ds a) (V : complexWhittakerModel t es (-a))
        (g : G (r + 1)) (g' : G (t + 1)),
        HasComplexPairNormalizedGrowth ds es a (complexCentralSign es ^ r)
          (complexUnequalIntegral h D (ρ g W.val) (ρ g' V.val))
          (fun s => ∫ p, complexUnequalDualKernel h (ρ g W.val) (ρ g' V.val) s p
            ∂complexUnequalDualMeasure (r := r) a D)

set_option maxHeartbeats 2400000 in
theorem complexUnequalTranslateGrowth : ComplexUnequalTranslateGrowthStatement := by
  intro r t h ds es hds hes a D hN W V g g'
  let u := ρ g W.val
  let v := ρ g' V.val
  let K := complexUnequalIntegrand h u v
  let Kd := complexUnequalDualKernel h u v
  let μ := D.measure
  let ν := complexUnequalDualMeasure (r := r) a D
  let R := Q t × Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℂ
  let δ := quotientDetAbs (t := t)
  let δd (p : R) := δ p.1
  let S := complexCentralSign es ^ r
  let : SigmaFinite μ := sigmaFinite_quotient D
  let : (rectangularMeasure (complexSelfDualMeasure a) (r - (t + 1)) (t + 1)).IsAddHaarMeasure :=
    rectangularMeasure_isAddHaar _ _ _
  let : SigmaFinite ν := by dsimp only [ν, complexUnequalDualMeasure]; infer_instance
  have hS : S ≠ 0 := pow_ne_zero _ (by
    have h := complexCentralSign_sq es
    intro hz
    rw [hz, zero_pow (by decide : 2 ≠ 0)] at h
    exact zero_ne_one h)
  have hu : HasLeftCharacter a u := hasLeftCharacter_of_rightTranslate W g
  have hv : HasLeftCharacter (-a) v := hasLeftCharacter_of_rightTranslate V g'
  have huc : Continuous u := (contMDiff_of_mem_complexWhittakerModel W.2).continuous.comp (continuous_id.mul_const g)
  have hvc : Continuous v := (contMDiff_of_mem_complexWhittakerModel V.2).continuous.comp (continuous_id.mul_const g')
  have hK (s : ℂ) : Continuous (K s) := continuous_ordinaryKernel h hu hv huc hvc s
  have hKd (s : ℂ) : Continuous (Kd s) := continuous_dualKernel h hu hv huc hvc s
  obtain ⟨b, hb, hbd⟩ := translatedUnequalDomination h a D W V {g} {g'} isCompact_singleton isCompact_singleton
  have hint (s : ℂ) (hs : b < s.re) : Integrable (K s) μ ∧ Integrable (Kd s) ν := by
    obtain ⟨B, hB, hb'⟩ := hb s.re
    obtain ⟨Bd, hBd, hbd'⟩ := hbd s.re
    have hm : (g, g', s) ∈ ({g} : Set (G (r + 1))) ×ˢ (({g'} : Set (G (t + 1))) ×ˢ univ) := by simp
    have hBounds (p : Q t) : ‖K s p‖ ≤ B p := hb' (g, g', s) hm hs le_rfl p
    have hBoundd (p : R) : ‖Kd s p‖ ≤ Bd p := hbd' (g, g', s) hm hs le_rfl p
    exact ⟨hB.mono' (hK s).aestronglyMeasurable (ae_of_all μ hBounds),
      hBd.mono' (hKd s).aestronglyMeasurable (ae_of_all ν hBoundd)⟩
  have hz (s : ℂ) (p : Q t) : K s p = K 0 p * (δ p : ℂ) ^ s :=
    complexUnequalIntegrand_eq_mul h u v s p
  have hzd (s : ℂ) (p : R) : Kd s p = Kd 0 p * (δd p : ℂ) ^ s :=
    complexUnequalDualKernel_eq_mul h u v s p
  have hδ (p : Q t) : 0 < δ p := quotientDetAbs_pos p
  have hδd (p : R) : 0 < δd p := quotientDetAbs_pos p.1
  have hI (x : ℝ) (hx : b + 1 ≤ x) : Integrable (fun p => ‖K 0 p‖ * δ p ^ x) μ := by
    have hx' : b < (x : ℂ).re := by rw [Complex.ofReal_re]; linarith
    exact (hint x hx').1.norm.congr (ae_of_all μ (norm_kernel (K := K) (δ := δ) hδ hz x))
  have hId (x : ℝ) (hx : b + 1 ≤ x) : Integrable (fun p => ‖Kd 0 p‖ * δd p ^ x) ν := by
    have hx' : b < (x : ℂ).re := by rw [Complex.ofReal_re]; linarith
    exact (hint x hx').2.norm.congr (ae_of_all ν (norm_kernel (K := Kd) (δ := δd) hδd hzd x))
  let f := ordinaryWeight ds es a S 1 0
  let fd := reflectedWeight ds es 1 0
  obtain ⟨hfm, hfdm, hf, hfd, hfM, hfdM⟩ := complexWeights_data ds es a S (rate := 1) one_pos 0
  obtain ⟨B, hB, w, hw⟩ := exists_whittakerIntertwiner_value r ds hds a W
  obtain ⟨Bd, hBd, w', hw'⟩ := exists_whittakerIntertwiner_value t es hes (-a) V
  have hθ (x : ℝ) (hx : 0 < x) : theta μ (K 0) δ f x = (x : ℂ) * theta ν (Kd 0) δd fd x⁻¹ := by
    have ht := (complexUnequalWeightedTranslation r t h ds es a D hN B Bd hB hBd w w' g g' 1 0 one_pos hx).2.2
    rw [hw, hw'] at ht
    unfold theta
    rw [← integral_const_mul]
    simpa only [weightedOrdinary, weightedDual, K, Kd, u, v, μ, ν, δd, S, f, fd, mul_left_comm] using ht
  have hG := complexThetaNormalizedGrowth μ ν (K 0) (Kd 0) δ δd
    (hK 0).aestronglyMeasurable (hKd 0).aestronglyMeasurable continuous_quotientDetAbs.measurable
    (continuous_quotientDetAbs.measurable.comp measurable_fst) hδ hδd
    (b + 1) hI hId ds es a S hS f fd hfm hfdm hf hfd
    (by simpa only [ArchimedeanInverseMellin.gaussianFactor, Complex.ofReal_one, Complex.ofReal_zero,
      one_mul, zero_mul, add_zero] using hfM)
    (by simpa only [ArchimedeanInverseMellin.gaussianFactor, Complex.ofReal_one, Complex.ofReal_zero,
      one_mul, zero_mul, add_zero] using hfdM) hθ
  exact ComplexThetaNormalizedGrowth.normalizedGrowth_congr_right hG ⟨b, fun s _ => ⟨
    integral_congr_ae (ae_of_all _ fun p => (hz s p).symm),
    integral_congr_ae (ae_of_all _ fun p => (hzd s p).symm)⟩⟩

end Langlands.Global.RankinSelbergGlobal.ComplexUnequalWeightedTranslation
