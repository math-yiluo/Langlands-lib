import Langlands.Analysis.Local.QuotientMeasureExistence
import Langlands.Global.RankinSelberg.ComplexJacquetCanonicalRange
import Langlands.Global.RankinSelberg.ComplexLocalAdjacentOpposite
import Langlands.Global.RankinSelberg.ComplexLocalEqualGeneratorTrace
import Langlands.Global.RankinSelberg.ComplexLocalEqualSquareLimit

/-! # The equal-rank successor step with strip growth -/

noncomputable section

open MeasureTheory Set
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open Langlands.Analysis.SchwartzMatrixNorm (EntrySchwartz OperatorSchwartz operatorToEntry)
open scoped NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

/-- Entire normalized equal-rank equations and strip growth at the standard character. -/
def ComplexLocalEqualGrowthAtRank (r : ℕ) : Prop :=
  ∀ (ds es : List ComplexCharacterData), ds.length = r + 1 → es.length = r + 1 →
  ∀ (D : ComplexQuotientMeasureData r) (W V : Langlands.GeneralLinear (r + 1) ℂ → ℂ)
    (Φ : 𝓢(Fin (r + 1) → ℂ, ℂ)),
    W ∈ complexWhittakerModel r ds 1 → V ∈ complexWhittakerModel r es (-1) →
    HasComplexPairNormalizedGrowth ds es 1 (complexCentralSign es ^ r)
      (complexEqualIntegral D W V Φ) (complexEqualDualIntegral 1 D W V Φ)

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation

open ArchimedeanLocal ComplexJacquet
open Langlands.Archimedean (characterOfParams)
open Langlands.GodementJacquet (complexMatrixFourier)
open ComplexGodement (HasFullRowRank SmallerProfile smallerWeights smallerExponents)
open ComplexCompactProfileFamily (characterList)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}
local notation "m" => r + 1
local notation "n" => r + 1 + 1
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Row" => Fin n → ℂ
local notation "Rect" => Matrix (Fin m) (Fin n) ℂ
local notation "L" => Fin n → ℤ
local notation "P" => Fin n → ℂ
local notation "Q" => Langlands.RankinSelberg.LeftUnipotentQuotient (r + 1) ℂ
local notation "Std[" l "," p "]" => Automorphic.complexStandardKFinite n (characterList l p)

private theorem stripGrowth_constant (c : ℂ) : HasStripExponentialGrowth (fun _ => c) :=
  fun _ _ => ⟨‖c‖, 0, 0, norm_nonneg _, le_rfl, fun _ _ _ _ => by simp⟩

private theorem stripGrowth_add {f g : ℂ → ℂ} (hf : HasStripExponentialGrowth f)
    (hg : HasStripExponentialGrowth g) : HasStripExponentialGrowth (f + g) := by
  intro a b
  obtain ⟨C, K, T, hC, hK, hF⟩ := hf a b
  obtain ⟨D, J, U, hD, _, hG⟩ := hg a b
  refine ⟨C + D, max K J, max T U, add_nonneg hC hD, hK.trans (le_max_left _ _), ?_⟩
  intro s ha hb hs
  rw [Pi.add_apply, add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (hF s ha hb ((le_max_left _ _).trans hs)).trans ?_
    gcongr
    exact le_max_left _ _
  · refine (hG s ha hb ((le_max_right _ _).trans hs)).trans ?_
    gcongr
    exact le_max_right _ _

private def growingKernelPairs {X : Type*} [MeasurableSpace X] (μ : Measure X) (A Ad E : ℂ → ℂ) :
    Submodule ℂ ((ℂ → X → ℂ) × (ℂ → X → ℂ)) where
  carrier := {K | ∃ (σ : ℝ) (N Nd : ℂ → ℂ),
    Differentiable ℂ N ∧ Differentiable ℂ Nd ∧
    HasStripExponentialGrowth N ∧ HasStripExponentialGrowth Nd ∧
    (∀ s : ℂ, σ < s.re →
      Integrable (K.1 s) μ ∧ Integrable (K.2 s) μ ∧
      N s = A s * (∫ x, K.1 s x ∂μ) ∧ Nd s = Ad s * (∫ x, K.2 s x ∂μ)) ∧
    ∀ s : ℂ, Nd (1 - s) = E s * N s}
  zero_mem' := by
    refine ⟨0, 0, 0, differentiable_const 0, differentiable_const 0,
      stripGrowth_constant 0, stripGrowth_constant 0, ?_, ?_⟩ <;> simp
  add_mem' := by
    rintro K P₁ ⟨σK, NK, NKd, hNK, hNKd, hgK, hgKd, hK, hKE⟩ ⟨σP, NP, NPd, hNP, hNPd, hgP, hgPd, hP, hPE⟩
    refine ⟨max σK σP, NK + NP, NKd + NPd, hNK.add hNP, hNKd.add hNPd,
      stripGrowth_add hgK hgP, stripGrowth_add hgKd hgPd, ?_, ?_⟩
    · intro s hs
      obtain ⟨hK₁, hK₂, hK₃, hK₄⟩ := hK s ((le_max_left _ _).trans_lt hs)
      obtain ⟨hP₁, hP₂, hP₃, hP₄⟩ := hP s ((le_max_right _ _).trans_lt hs)
      refine ⟨hK₁.add hP₁, hK₂.add hP₂, ?_, ?_⟩
      · simp only [Prod.fst_add, Pi.add_apply, hK₃, hP₃, integral_add hK₁ hP₁, mul_add]
      · simp only [Prod.snd_add, Pi.add_apply, hK₄, hP₄, integral_add hK₂ hP₂, mul_add]
    · intro s
      simp only [Pi.add_apply, hKE s, hPE s, mul_add]
  smul_mem' := by
    rintro c K ⟨σ, N, Nd, hN, hNd, hg, hgd, hK, hE⟩
    refine ⟨σ, c • N, c • Nd, hN.const_mul c, hNd.const_mul c,
      (stripGrowth_constant c).mul hg, (stripGrowth_constant c).mul hgd, ?_, ?_⟩
    · intro s hs
      obtain ⟨hK₁, hK₂, hK₃, hK₄⟩ := hK s hs
      refine ⟨hK₁.const_mul c, hK₂.const_mul c, ?_, ?_⟩
      · change c * N s = A s * (∫ x, c * K.1 s x ∂μ)
        rw [hK₃, integral_const_mul]
        ring
      · change c * Nd s = Ad s * (∫ x, c * K.2 s x ∂μ)
        rw [hK₄, integral_const_mul]
        ring
    · intro s
      simp only [Pi.smul_apply, smul_eq_mul, hE s]
      ring

private def equalKernelPair (V : G → ℂ) (φ : 𝓢(Row, ℂ)) :
    (G → ℂ) →ₗ[ℂ] ((ℂ → Q → ℂ) × (ℂ → Q → ℂ)) where
  toFun W := (complexEqualIntegrand W V φ,
    complexEqualIntegrand (ArchimedeanLocal.dualFunction n W) (ArchimedeanLocal.dualFunction n V)
      (complexFourierTransform 1 φ))
  map_add' := by
    intros
    apply Prod.ext <;> funext s x <;>
      simp [complexEqualIntegrand, ArchimedeanLocal.equalIntegrand, ArchimedeanLocal.dualFunction, add_mul]
  map_smul' := by
    intros
    apply Prod.ext <;> funext s x <;>
      simp [complexEqualIntegrand, ArchimedeanLocal.equalIntegrand, ArchimedeanLocal.dualFunction, mul_assoc]

/-- Compatible complex group and unipotent quotient measures exist at each positive rank. -/
theorem exists_smallerQuotientData : Nonempty (ComplexQuotientMeasureData r) := by
  let U := GeneralLinear.upperUnipotent m ℂ
  let t := RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) m
  let : LocallyCompactSpace H := t.locallyCompactSpace
  let : SecondCountableTopology H := t.secondCountableTopology
  let : LocallyCompactSpace U := GeneralLinear.UpperUnipotent.locallyCompactSpace
  let : SecondCountableTopology U := Topology.IsInducing.subtypeVal.secondCountableTopology
  have : Nonempty (TopologicalSpace.PositiveCompacts H) := TopologicalSpace.PositiveCompacts.nonempty'
  let κ := Classical.arbitrary (TopologicalSpace.PositiveCompacts H)
  let μ := Measure.haarMeasure κ
  let ν := ComplexJacquetUnipotentMeasure.entryHaar (complexSelfDualMeasure 1) m
  let : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure κ
  let : ν.IsHaarMeasure := ComplexJacquetUnipotentMeasure.entryHaar_isHaar _ _
  let : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  let : ν.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν
  let : μ.IsMulRightInvariant := Archimedean.isMulRightInvariant_archimedeanGL ℂ m μ
  let : ν.IsMulRightInvariant := ComplexJacquetChamberIntertwiner.entryHaar_isMulRightInvariant _ r
  obtain ⟨μq, hμq⟩ := Langlands.QuotientIntegration.compatibleMeasureExists U
    (GeneralLinear.UpperUnipotent.isClosed (R := ℂ)) μ ν
  exact ⟨⟨μ, inferInstance, ν, inferInstance, inferInstance, μq, hμq⟩⟩

open scoped Matrix.Norms.Elementwise in
private theorem compactGenerator_growth (hAdj : ComplexLocalAdjacentGrowthAtRank r (-1))
    (D : ComplexQuotientMeasureData (r + 1)) (D₁ : ComplexQuotientMeasureData r)
    (l l' : L) (q : Fin m → ℂ) (p' : P) (Φ : OperatorSchwartz m n)
    (hΦ : HasCompactSupport Φ) (hfull : ∀ X ∈ tsupport Φ, HasFullRowRank X)
    (f : SmallerProfile l) (f' : Std[l', p']) (φ : 𝓢(Row, ℂ)) (z : ℂ) :
    let W := recursiveJacquetCoefficient D₁ (-1) l (Fin.cons z q) Φ f
    let V := continuedJacquet (complexSelfDualMeasure 1) 1 l' p' f'
    HasComplexPairNormalizedGrowth (characterList l (Fin.cons z q)) (characterList l' p') 1
      (complexCentralSign (characterList l' p') ^ m)
      (complexEqualIntegral D W V φ) (complexEqualDualIntegral 1 D W V φ) := by
  let e (i : Fin n) := characterOfParams (l' i) (p' i)
  let ds := characterList (smallerWeights l) q
  let d := characterOfParams (l 0) 0
  let μ := complexSelfDualMeasure 1
  let U : complexWhittakerModel r ds 1 :=
    ⟨canonicalJacquetFamily μ (-1) (smallerWeights l) f.val f.2 q, by
      simpa only [μ, ds, Langlands.GodementJacquet.complexSelfDualMeasure_neg_scale, neg_neg] using
        canonicalJacquetProfile_mem (-1) l q f⟩
  let B := continuedJacquet μ 1 l' p'
  let Ψ := complexSquareProductSchwartz (operatorToEntry Φ) φ
  have hΨ : (Ψ : Matrix (Fin n) (Fin n) ℂ → ℂ) = complexSquareProductTest (operatorToEntry Φ) φ :=
    funext (complexSquareProductSchwartz_apply _ _)
  obtain ⟨T, hT⟩ := @complexLocalSquareFourierSchwartz n 1
  have hds : ds.length = m := List.length_ofFn
  obtain ⟨F, hF, hg, ⟨τ, σ, h⟩, τd, σd, hd⟩ := complexLocalEqualSquareLimit (r := r)
    D D₁ d ds hds e U B (complexJacquetCanonicalIntertwiner μ 1 l' p') f'
    Ψ (T Ψ) (hT Ψ) (fun V => hAdj (List.ofFn e) ds List.length_ofFn hds D₁ V.val U.val V.2
      (by simpa only [neg_neg] using U.2))
  refine complexLocalEqualGeneratorTrace D D₁ l l' q p' Φ hΦ hfull f f' φ
    ⟨F, τ, σ, τd, σd, hF, hg, ?_, ?_⟩ z
  · simpa only [hΨ, d, ds, e, B, μ, U, characterList] using h
  · simpa only [hT Ψ, hΨ, d, ds, e, B, μ, U, characterList] using hd

open scoped Matrix.Norms.Operator in
private theorem canonicalEqualGrowth_succ (hAdj : ComplexLocalAdjacentGrowthAtRank r 1)
    (D : ComplexQuotientMeasureData (r + 1)) (l l' : L) (p p' : P)
    (f : Std[l, p]) (f' : Std[l', p']) (φ : 𝓢(Row, ℂ)) :
    let W := continuedJacquet (complexSelfDualMeasure 1) (-1) l p f
    let V := continuedJacquet (complexSelfDualMeasure 1) 1 l' p' f'
    HasComplexPairNormalizedGrowth (characterList l p) (characterList l' p') 1
      (complexCentralSign (characterList l' p') ^ m)
      (complexEqualIntegral D W V φ) (complexEqualDualIntegral 1 D W V φ) := by
  let D₁ := Classical.choice (exists_smallerQuotientData (r := r))
  let μ := complexSelfDualMeasure 1
  let ds := characterList l p
  let es := characterList l' p'
  let W := continuedJacquet μ (-1) l p f
  let V := continuedJacquet μ 1 l' p' f'
  let A := (complexPairLFactor ds es).denominator
  let Ad := (complexPairLFactor (ds.map ComplexCharacterData.inv) (es.map ComplexCharacterData.inv)).denominator
  let E (s : ℂ) := complexCentralSign es ^ m *
    (complexPairEpsilon ds es 1 ‖((1 : ℂˣ) : ℂ)‖₊ (nnnorm_pos.mpr (1 : ℂˣ).ne_zero) s : ℂ)
  let K := equalKernelPair V φ
  let T := (growingKernelPairs D.measure A Ad E).comap K
  have hSpan : Submodule.span ℂ (compactRecursiveGenerators D₁ (-1) l p) ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨Φ, u, hΦ, hfull, rfl⟩
    let q := smallerExponents p
    let z := p 0
    have hp : Fin.cons (α := fun _ : Fin n => ℂ) z q = p := Fin.cons_self_tail p
    have hg := compactGenerator_growth (complexLocalAdjacentOppositeGrowth hAdj)
      D D₁ l l' q p' Φ hΦ hfull u f' φ z
    obtain ⟨σ, hI, _, _⟩ := complexLocalEqualGeneratorFamily 1 D D₁ l l' q p' Φ hΦ hfull u f' φ (‖z‖ + 1)
    have hz : z ∈ Metric.ball (0 : ℂ) (‖z‖ + 1) := by
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_add_one _
    have hInt := hI z hz
    dsimp only at hInt hg
    rw [hp] at hInt hg
    obtain ⟨N, Nd, hN, hNd, hNg, hNdg, ⟨τ, hτ⟩, hE⟩ := hg
    refine ⟨max σ τ, N, Nd, hN, hNd, hNg, hNdg, ?_, hE⟩
    intro s hs
    exact ⟨(hInt s ((le_max_left _ _).trans_lt hs)).1, (hInt s ((le_max_left _ _).trans_lt hs)).2,
      (hτ s ((le_max_right _ _).trans_lt hs)).1, (hτ s ((le_max_right _ _).trans_lt hs)).2⟩
  have hW : W ∈ Submodule.span ℂ (compactRecursiveGenerators D₁ (-1) l p) := by
    apply complexJacquetCompactRecursiveSpan D₁ (-1) l p
    simpa only [W, μ, Langlands.GodementJacquet.complexSelfDualMeasure_neg_scale] using
      (show continuedJacquet (complexSelfDualMeasure (-1)) (-1) l p f ∈
        LinearMap.range (continuedJacquet (complexSelfDualMeasure (-1)) (-1) l p) from ⟨f, rfl⟩)
  obtain ⟨σ, N, Nd, hN, hNd, hNg, hNdg, hR, hF⟩ := hSpan hW
  exact ⟨N, Nd, hN, hNd, hNg, hNdg, ⟨σ, fun s hs => ⟨(hR s hs).2.2.1, (hR s hs).2.2.2⟩⟩, hF⟩

/-- The adjacent step supplies the normalized equation and strip growth in the next
larger equal rank, provided the Whittaker model equals the canonical range. -/
def ComplexLocalEqualGrowthStepStatement : Prop :=
  ComplexJacquetIdentityProportionality → ComplexLocalAdjacentGrowthAtRank r 1 →
    ComplexLocalEqualGrowthAtRank (r + 1)

set_option maxHeartbeats 550000 in
theorem complexLocalEqualGrowthStep : ComplexLocalEqualGrowthStepStatement (r := r) := by
  intro hRange hAdj ds es hds hes D W V φ hW hV
  let μ := complexSelfDualMeasure 1
  obtain ⟨l, p, rfl, hds'⟩ := complexJacquetCanonicalRange hRange (r + 1) μ (-1) ds hds
  obtain ⟨l', p', rfl, hes'⟩ := complexJacquetCanonicalRange hRange (r + 1) μ 1 es hes
  rw [neg_neg] at hds'
  rw [hds'] at hW
  rw [hes'] at hV
  obtain ⟨f, rfl⟩ := hW
  obtain ⟨f', rfl⟩ := hV
  exact canonicalEqualGrowth_succ hAdj D l l' p p' f f' φ

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation
