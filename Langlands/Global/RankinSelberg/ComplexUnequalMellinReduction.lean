import Langlands.Global.RankinSelberg.ArchimedeanComplexPairFactor
import Langlands.Global.RankinSelberg.ArchimedeanRealPairIdentity
import Langlands.Global.RankinSelberg.ComplexLocalUnequalFromNormalized

/-! # From complex unequal-rank Mellin pair identities to the local equation -/

noncomputable section

open MeasureTheory
open scoped NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexUnequalMellinReduction

open Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient rectangularMeasure_isAddHaar)
open ArchimedeanLocal
open ArchimedeanMellinPair (theta RapidDecay mellin_theta_entire)
open ArchimedeanRealPairIdentity (PairIdentity theta_eq_of_pairIdentity norm_kernel kernel_zero_eq
  ofReal_cpow_eq_exp)
open ArchimedeanComplexPairFactor (complexPairMellinFactor)

attribute [local instance] archimedeanComplexGLMeasurable archimedeanComplexGLBorel
  archimedeanComplexNMeasurable archimedeanComplexNBorel
  archimedeanComplexQMeasurable archimedeanComplexQBorel

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "Q" => fun t => LeftUnipotentQuotient t ℂ
local notation "Δ" => fun g => complexNormalizedAbs (Matrix.det (Units.val g))

/-- The complex normalized determinant on the smaller left-unipotent quotient. -/
def quotientDetAbs {t : ℕ} (q : Q t) : ℝ := Δ q.out

theorem quotientDetAbs_pos {t : ℕ} (q : Q t) : 0 < quotientDetAbs q :=
  pow_pos (norm_pos_iff.mpr q.out.det_ne_zero) _

theorem continuous_quotientDetAbs {t : ℕ} : Continuous (quotientDetAbs (t := t)) := by
  let δ : Q t → ℂ := Langlands.QuotientIntegration.descend
    (Langlands.GeneralLinear.upperUnipotent (t + 1) ℂ) (fun g => Matrix.det g.val) fun u g => by
      change Matrix.det (u.val.val * g.val) = _
      rw [Matrix.det_mul, Langlands.RankinSelberg.unipotent_det, one_mul]
  have hδ : Continuous δ := by
    unfold δ Langlands.QuotientIntegration.descend
    exact Units.continuous_val.matrix_det.quotient_lift _
  have hq (q : Q t) : δ q = q.out.val.det := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have he : quotientDetAbs (t := t) = fun q => ‖δ q‖ ^ 2 := by
    funext q
    rw [hq]
    rfl
  rw [he]
  exact hδ.norm.pow 2

private theorem detPower_shift {n : ℕ} (g : G n) (s b : ℂ) :
    ArchimedeanLocal.detPower complexNormalizedAbs g (s - b) =
      ArchimedeanLocal.detPower complexNormalizedAbs g (0 - b) * ((Δ g : ℝ) : ℂ) ^ s := by
  have hpos : 0 < Δ g := pow_pos (norm_pos_iff.mpr g.det_ne_zero) _
  rw [ofReal_cpow_eq_exp hpos]
  unfold ArchimedeanLocal.detPower
  rw [← Complex.exp_add]
  congr 1
  ring

/-- The determinant is the Mellin variable for the ordinary complex unequal kernel. -/
theorem complexUnequalIntegrand_eq_mul {r t : ℕ} (h : t < r) (W : G (r + 1) → ℂ)
    (V : G (t + 1) → ℂ) (s : ℂ) (q : Q t) :
    complexUnequalIntegrand h W V s q =
      complexUnequalIntegrand h W V 0 q * (quotientDetAbs q : ℂ) ^ s := by
  simp only [complexUnequalIntegrand, ArchimedeanLocal.unequalIntegrand,
    detPower_shift q.out s, quotientDetAbs, mul_assoc]

/-- The same smaller quotient determinant is the Mellin variable for the block kernel. -/
theorem complexUnequalDualKernel_eq_mul {r t : ℕ} (h : t < r) (W : G (r + 1) → ℂ)
    (V : G (t + 1) → ℂ) (s : ℂ) (p : Q t × Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℂ) :
    complexUnequalDualKernel h W V s p =
      complexUnequalDualKernel h W V 0 p * (quotientDetAbs p.1 : ℂ) ^ s := by
  simp only [complexUnequalDualKernel, ArchimedeanLocal.blockKernel,
    detPower_shift p.1.out s, quotientDetAbs, mul_assoc]

/-- Jacquet's radial pair identity for the two actual unequal-rank kernels. -/
def ComplexUnequalPairIdentity {r t : ℕ} (h : t < r) (ds es : List ComplexCharacterData)
    (a : ℂˣ) (D : ComplexQuotientMeasureData t) (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ) : Prop :=
  PairIdentity D.measure (complexUnequalDualMeasure (r := r) a D)
    (complexUnequalIntegrand h W V 0) quotientDetAbs
    (complexUnequalDualKernel h W V 0) (fun p => quotientDetAbs p.1)
    (complexPairLFactor ds es).denominator
    (complexPairLFactor (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)).denominator
    (fun s => (complexPairEpsilon ds es a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ))
    (complexCentralSign es ^ r)

private theorem complexCentralSign_ne_zero (ds : List ComplexCharacterData) : complexCentralSign ds ≠ 0 := by
  induction ds with
  | nil => simp [complexCentralSign]
  | cons d ds ih =>
    exact mul_ne_zero (d.character (-1)).ne_zero ih

private theorem sigmaFinite_quotient {t : ℕ} (D : ComplexQuotientMeasureData t) : SigmaFinite D.measure := by
  let e := Langlands.QuotientIntegration.leftQuotient_isOpenQuotientMap
    (Langlands.GeneralLinear.upperUnipotent (t + 1) ℂ)
  let : SecondCountableTopology (G (t + 1)) :=
    (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) (t + 1)).isInducing.secondCountableTopology
  let : LocallyCompactSpace (G (t + 1)) :=
    (Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) (t + 1)).locallyCompactSpace
  let : SigmaCompactSpace (G (t + 1)) := sigmaCompactSpace_of_locallyCompact_secondCountable
  let : SigmaCompactSpace (Q t) := by
    apply isSigmaCompact_univ_iff.mp
    rw [← Set.range_eq_univ.mpr e.surjective]
    exact isSigmaCompact_range e.continuous
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  infer_instance

private theorem halfPlane_mellinData {X : Type} [MeasurableSpace X] (μ : Measure X)
    (A : ℂ → X → ℂ) (δ : X → ℝ) (hδm : Measurable δ) (hδ : ∀ x, 0 < δ x)
    (hA : ∀ s x, A s x = A 0 x * (δ x : ℂ) ^ s) (σ : ℝ)
    (hI : ∀ s : ℂ, σ < s.re → Integrable (A s) μ) :
    AEStronglyMeasurable (A 0) μ ∧
      ∀ b : ℝ, σ + 1 ≤ b → Integrable (fun x => ‖A 0 x‖ * δ x ^ b) μ := by
  have hb (b : ℝ) (hb : σ + 1 ≤ b) : σ < ((b : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    linarith
  refine ⟨?_, fun b h => (hI b (hb b h)).norm.congr (ae_of_all _ (norm_kernel hδ hA b))⟩
  let b : ℂ := (σ + 1 : ℝ)
  have hM : Measurable (fun x => (δ x : ℂ) ^ (-b)) :=
    (Complex.measurable_ofReal.comp hδm).pow_const _
  exact ((hI b (hb (σ + 1) le_rfl)).aestronglyMeasurable.mul hM.aestronglyMeasurable).congr
    (ae_of_all _ fun x => (kernel_zero_eq hδ hA b x).symm)

/-- The Mellin-pair identity gives the entire normalized complex equation on each fixed pair.
The only division in the entire functions is by products of nonvanishing factors. -/
theorem normalized_of_complexUnequalPairIdentity {r t : ℕ} (h : t < r)
    (ds es : List ComplexCharacterData) (a : ℂˣ) (D : ComplexQuotientMeasureData t)
    (W : complexWhittakerModel r ds a) (V : complexWhittakerModel t es (-a))
    (hPair : ComplexUnequalPairIdentity h ds es a D W.val V.val) :
    ∃ (σ : ℝ) (N Nd : ℂ → ℂ), Differentiable ℂ N ∧ Differentiable ℂ Nd ∧
      (∀ s : ℂ, σ < s.re →
        N s = (complexPairLFactor ds es).denominator s * complexUnequalIntegral h D W.val V.val s ∧
        Nd s = (complexPairLFactor (ds.map ComplexCharacterData.inv)
          (es.map ComplexCharacterData.inv)).denominator s * complexUnequalDualIntegral h a D W.val V.val s) ∧
      ∀ s : ℂ, Nd (1 - s) = complexCentralSign es ^ r *
        (complexPairEpsilon ds es a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ) * N s := by
  let μ := D.measure
  let μ' := complexUnequalDualMeasure (r := r) a D
  let A := complexUnequalIntegrand h W.val V.val
  let A' := complexUnequalDualKernel h W.val V.val
  let δ := quotientDetAbs (t := t)
  let δ' : Q t × Matrix (Fin (r - (t + 1))) (Fin (t + 1)) ℂ → ℝ := δ ∘ Prod.fst
  let E s := (complexPairEpsilon ds es a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ)
  let sign := complexCentralSign es ^ r
  let : SigmaFinite μ := sigmaFinite_quotient D
  let : (Langlands.RankinSelberg.rectangularMeasure (complexSelfDualMeasure a) (r - (t + 1)) (t + 1)).IsAddHaarMeasure :=
    rectangularMeasure_isAddHaar _ _ _
  let : SigmaFinite μ' := by
    dsimp only [μ', complexUnequalDualMeasure]
    infer_instance
  have hδm : Measurable δ := continuous_quotientDetAbs.measurable
  have hδ'm : Measurable δ' := hδm.comp measurable_fst
  have hδp : ∀ q, 0 < δ q := quotientDetAbs_pos
  have hδ'p : ∀ p, 0 < δ' p := fun p => hδp p.1
  obtain ⟨σ, hI⟩ := complexLocalUnequalConvergence h ds es a D W V
  obtain ⟨hA, hM⟩ := halfPlane_mellinData μ A δ hδm hδp
    (complexUnequalIntegrand_eq_mul h W.val V.val) σ (fun s hs => (hI s hs).1)
  obtain ⟨hA', hM'⟩ := halfPlane_mellinData μ' A' δ' hδ'm hδ'p
    (complexUnequalDualKernel_eq_mul h W.val V.val) σ (fun s hs => (hI s hs).2)
  have hsign : sign ≠ 0 := pow_ne_zero _ (complexCentralSign_ne_zero es)
  obtain ⟨_, f, f', hf, hf', hfd, hf'd, hfM, hf'M, _, _, _⟩ :=
    complexPairMellinFactor ds es a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) sign hsign
  have htheta (b : ℝ) (hb : 0 < b) := theta_eq_of_pairIdentity hPair hf hf' hfd hf'd hfM hf'M hb
  obtain ⟨hEntire, hOrdinary, hDual⟩ := mellin_theta_entire μ μ' (A 0) δ (A' 0) δ' hA hA' hδm hδ'm hδp hδ'p
    f f' hf hf' hfd hf'd (σ + 1) hM hM' htheta
  let T s := mellin (theta μ (A 0) δ f) (-s)
  let J (s : ℂ) := Complex.exp (s ^ 2)
  have hJ : Differentiable ℂ J := (differentiable_id.pow 2).cexp
  have hE : Differentiable ℂ E := differentiable_complexEpsilon _ _ _ _
  have hJ₀ (s : ℂ) : J s ≠ 0 := Complex.exp_ne_zero _
  have hE₀ (s : ℂ) : E s ≠ 0 := Units.ne_zero _
  have hden (s : ℂ) : sign * E s * J s ≠ 0 := mul_ne_zero (mul_ne_zero hsign (hE₀ s)) (hJ₀ s)
  refine ⟨σ + 1, fun s => T s / (sign * E s * J s), fun s => T (1 - s) / J (1 - s),
    hEntire.div ((hE.const_mul sign).mul hJ) hden,
    (hEntire.div hJ hJ₀).comp (differentiable_id.const_sub 1), ?_, ?_⟩
  · intro s hs
    have hσs : σ < s.re := by linarith
    have hOrd : (∫ q, A 0 q * (δ q : ℂ) ^ s ∂μ) = complexUnequalIntegral h D W.val V.val s := by
      change _ = ∫ q, A s q ∂μ
      exact integral_congr_ae (ae_of_all _ fun q => (complexUnequalIntegrand_eq_mul h W.val V.val s q).symm)
    have hRef : (∫ p, A' 0 p * (δ' p : ℂ) ^ s ∂μ') = complexUnequalDualIntegral h a D W.val V.val s := by
      rw [show complexUnequalDualIntegral h a D W.val V.val s = ∫ p, A' s p ∂μ'
        from (integral_prod _ (hI s hσs).2).symm]
      exact integral_congr_ae (ae_of_all _ fun p => (complexUnequalDualKernel_eq_mul h W.val V.val s p).symm)
    constructor
    · change T s / (sign * E s * J s) = _
      dsimp only [T]
      rw [hOrdinary s hs.le, hOrd, hfM]
      change _ * (sign * E s * J s * _) / (sign * E s * J s) = _
      apply (div_eq_iff (hden s)).2
      ring
    · have hs' : (1 - s).re ≤ 1 - (σ + 1) := by simp only [Complex.sub_re, Complex.one_re]; linarith
      change T (1 - s) / J (1 - s) = _
      dsimp only [T]
      rw [hDual (1 - s) hs', sub_sub_cancel, hRef, hf'M, sub_sub_cancel]
      change _ * (J (1 - s) * _) / J (1 - s) = _
      apply (div_eq_iff (hJ₀ (1 - s))).2
      ring
  · intro s
    change T (1 - (1 - s)) / J (1 - (1 - s)) = sign * E s * (T s / (sign * E s * J s))
    rw [sub_sub_cancel]
    field_simp [hsign, hE₀ s, hJ₀ s]

/-- It suffices to establish the exact radial pair identities on the two finite Whittaker models. -/
def ComplexUnequalMellinPairIdentityStatement : Prop :=
  ∀ (r t : ℕ) (h : t < r) (ds es : List ComplexCharacterData), ds.length = r + 1 → es.length = t + 1 →
    ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData t)
      (W : complexWhittakerModel r ds a) (V : complexWhittakerModel t es (-a)),
      ComplexUnequalPairIdentity h ds es a D W.val V.val

/-- The Mellin pair identities on the exact models imply the published local equation. -/
def ComplexLocalUnequalFromMellinPairsStatement : Prop :=
  ComplexUnequalMellinPairIdentityStatement → ComplexLocalUnequalFunctionalEquationStatement

theorem complexLocalUnequalFromMellinPairs : ComplexLocalUnequalFromMellinPairsStatement := by
  intro hPair
  apply complexLocalUnequalFromNormalized
  intro r t h ds es hd he a D B B' hB hB' f f'
  let W : complexWhittakerModel r ds a :=
    ⟨B f, Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)⟩
  let V : complexWhittakerModel t es (-a) :=
    ⟨B' f', Submodule.mem_iSup_of_mem B' (Submodule.mem_iSup_of_mem hB' ⟨f', rfl⟩)⟩
  exact normalized_of_complexUnequalPairIdentity h ds es a D W V (hPair r t h ds es hd he a D W V)

end Langlands.Global.RankinSelbergGlobal.ComplexUnequalMellinReduction
