import Langlands.Analysis.Complex.PolynomialFiberContinuation
import Langlands.Global.RankinSelberg.ComplexAdjacentCanonical
import Langlands.Global.RankinSelberg.ComplexAdjacentGodementPolynomial
import Langlands.Global.RankinSelberg.ComplexJacquetMultiplicityOne
import Langlands.Global.RankinSelberg.ComplexRankZeroGaussianGeneration

/-! # Adjacent polynomial normalization from the lower equal rank -/

noncomputable section

open MeasureTheory Metric Set
open scoped Matrix.Norms.Operator SchwartzMap Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open ArchimedeanLocal Langlands.Archimedean Langlands.Automorphic Langlands.LocalFactor.Archimedean
open ComplexEqualPolynomialGeneration (IsGaussianPolynomialRow)
open ComplexAdjacentUnfolding (complexAdjacentGodementPolynomial complexUnequalOrdinaryKernel
  complexUnequalOrdinaryKernel_apply godementTest canonicalChamberRemoval quotient_sFinite
  differentiable_pairDenominator)
open ComplexGodement (addedCharacter smallerExponents smallerWeights characterList_cons
  gaussianGodementSections godementSection complexGodementGaussianSpanning)
open ComplexGodementGaussianPolynomial (gaussianPolynomial)
open ComplexCompactProfileFamily (characterList)
open ComplexJacquetChamberHolomorphic (chamber)
open ComplexJacquetContinuation (continuedJacquet complexJacquetIntertwiner
  continuedJacquet_mem_complexWhittakerModel complexJacquetSchwartzEvaluation transferProfile
  transferProfile_self complexUnequalCanonicalFamily)
open ComplexJacquetMultiplicityOne (complexJacquetMultiplicityOne exists_characterList)
open Langlands.Analysis.PolynomialFiberContinuation (polynomialFiberContinuation)
open Langlands.GeneralDirichlet (eqOn_halfPlane)
open FunctionalEquationComparison.CompletedEquationAdapter (complexPairLFactor_denominator_ne_zero)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

local notation "GLc" => fun n => Langlands.GeneralLinear n ℂ
private abbrev reciprocalPair (ds es : List ComplexCharacterData) (s : ℂ) :=
  ((complexPairLFactor ds es).denominator s)⁻¹
local notation "LFactor[" ds "," es "]" => reciprocalPair ds es

/-- All ordinary equal-rank tests with a standard Gaussian row have polynomial normalization. -/
def ComplexEqualPolynomialAtRank (r : ℕ) (a : ℂˣ) : Prop :=
  ∀ (ds es : List ComplexCharacterData), ds.length = r + 1 → es.length = r + 1 →
    ∀ (D : ComplexQuotientMeasureData r) (W : complexWhittakerModel r ds a)
      (V : complexWhittakerModel r es (-a)) (φ : 𝓢(Fin (r + 1) → ℂ, ℂ)),
      IsGaussianPolynomialRow (2 * Real.pi) φ →
      ∃ (N : OrdinaryIntegralNormalization (complexEqualIntegral D W.val V.val φ) LFactor[ds,es])
        (P : Polynomial ℂ), N.value = P.eval

/-- All ordinary adjacent-rank tests have polynomial normalization. -/
def ComplexAdjacentPolynomialAtRank (r : ℕ) (a : ℂˣ) : Prop :=
  ∀ (ds es : List ComplexCharacterData), ds.length = r + 2 → es.length = r + 1 →
    ∀ (D : ComplexQuotientMeasureData r) (W : complexWhittakerModel (r + 1) ds a)
      (V : complexWhittakerModel r es (-a)),
      ∃ (N : OrdinaryIntegralNormalization (complexUnequalIntegral (Nat.lt_succ_self r) D W.val V.val)
        LFactor[ds,es]) (P : Polynomial ℂ), N.value = P.eval

/-- Rank one supplies polynomial equal-rank normalizations at every trace scale. -/
theorem complexEqualPolynomialRankZero (a : ℂˣ) : ComplexEqualPolynomialAtRank 0 a := by
  intro ds es hds hes D W V φ hφ
  obtain ⟨P, N, hN⟩ := (ComplexRankZero.complexRankZeroGaussianGeneration ds es hds hes a D).1 (W, V, ⟨φ, hφ⟩)
  exact ⟨N, P, funext hN⟩

variable {r : ℕ}
local notation "m" => (r + 1 : ℕ)
local notation "n" => (r + 1 + 1 : ℕ)
local notation "P" => Fin n → ℂ
local notation "Q" => Fin m → ℂ
local notation "L" => Fin n → ℤ
local notation "H" => GLc m
local notation "G" => GLc n
local notation "gap" => Nat.lt_succ_self r

private def HasCanonicalAdjacentPolynomial (D : ComplexQuotientMeasureData r) (a : ℂˣ)
    (l : L) (p : P) (es : List ComplexCharacterData) (V : H → ℂ) : Prop :=
  ∀ f : complexStandardKFinite n (characterList l p),
    let W := continuedJacquet (complexSelfDualMeasure a) a l p f
    complexUnequalIntegrand gap W V ∈ polynomialOrdinaryKernels D.measure LFactor[characterList l p,es]

private theorem canonicalAdjacentPolynomial_chamber (D : ComplexQuotientMeasureData r)
    (a : ℂˣ) (ha : ‖(a : ℂ)‖ = 1) (hEqual : ComplexEqualPolynomialAtRank r (-a))
    (l : L) (q : Q) (e : Fin m → ComplexCharacterData)
    (B : complexStandardKFinite m (List.ofFn e) →ₗ[ℂ] (H → ℂ))
    (hB : IsComplexWhittakerIntertwiner r (List.ofFn e) a B) (v : complexStandardKFinite m (List.ofFn e)) :
    ∃ M : ℕ, ∀ p : P, smallerExponents p = q → p ∈ chamber (r + 1) →
      (m : ℝ) + M ≤ (p 0 + (((m : ℂ) + 1) / 2)).re →
      HasCanonicalAdjacentPolynomial D a l p (List.ofFn e) (B v) := by
  let : SFinite D.measure := quotient_sFinite D
  let ν := D.groupHaar
  let : ν.IsHaarMeasure := D.groupHaar_isHaar
  let : ν.IsMulRightInvariant := ComplexAdjacentUnfolding.complexAdjacent_groupHaar_rightInvariant D
  let ds := characterList (smallerWeights l) q
  obtain ⟨M, hM⟩ := complexGodementGaussianSpanning (r := r) ν
    (fun i => characterOfParams (smallerWeights l i) (q i))
  obtain ⟨N, hN⟩ := complexJacquetSchwartzEvaluation (r := r) ν l q
  refine ⟨max M N, fun p hq hp hb f => ?_⟩
  have hBound (k : ℕ) (hk : k ≤ max M N) :
      (m : ℝ) + k ≤ (p 0 + (((m : ℂ) + 1) / 2)).re :=
    (add_le_add le_rfl (by exact_mod_cast hk : (k : ℝ) ≤ (max M N : ℕ))).trans hb
  have hEval := hN p hq hp (hBound N (le_max_right _ _))
  subst q
  let d := addedCharacter l p
  let μ := complexSelfDualMeasure a
  let J := continuedJacquet μ a l p
  let J₀ := continuedJacquet μ a (smallerWeights l) (smallerExponents p)
  have hd : (m : ℝ) + M ≤ (d.exponent + (((m : ℂ) + 1) / 2)).re := by
    simpa only [d, addedCharacter, characterOfParams_exponent] using hBound M (le_max_left _ _)
  have hList : characterList l p = d :: ds := characterList_cons l p
  have hSpan : Submodule.span ℂ (gaussianGodementSections ν d ds) =
      complexStandardKFinite n (characterList l p) :=
    (hM d hd).trans (congrArg (complexStandardKFinite n) hList).symm
  let S := (polynomialOrdinaryKernels D.measure LFactor[characterList l p,List.ofFn e]).comap
    (complexUnequalOrdinaryKernel gap (B v))
  let T := (S.comap J).map (complexStandardKFinite n (characterList l p)).subtype
  have hT : Submodule.span ℂ (gaussianGodementSections ν d ds) ≤ T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨p₀, u⟩, rfl⟩
    let W₀ := godementSection ν d (gaussianPolynomial p₀) u.val
    have hW₀ : W₀ ∈ complexStandardKFinite n (characterList l p) := hSpan ▸
      (Submodule.subset_span (s := gaussianGodementSections ν d ds) ⟨(p₀, u), rfl⟩)
    let F : complexStandardKFinite n (characterList l p) := ⟨W₀, hW₀⟩
    refine ⟨F, ?_, rfl⟩
    let U : complexWhittakerModel r ds (-a) := ⟨J₀ u,
      continuedJacquet_mem_complexWhittakerModel μ a (smallerWeights l) (smallerExponents p) u⟩
    have hF : J F = godementTest D a d (gaussianPolynomial p₀) U.val :=
      hEval μ a (gaussianPolynomial p₀) u F rfl
    change complexUnequalIntegrand gap (J F) (B v) ∈
      polynomialOrdinaryKernels D.measure LFactor[characterList l p,List.ofFn e]
    rw [hF, hList]
    apply complexAdjacentGodementPolynomial D (ComplexDuality.unitaryHaar m) a ha d ds e
      List.length_ofFn U B hB v p₀
    intro V φ hφ
    let V₀ : complexWhittakerModel r (List.ofFn e) (-(-a)) := ⟨V, by simpa only [neg_neg] using V.2⟩
    exact hEqual ds (List.ofFn e) List.length_ofFn List.length_ofFn D U V₀ φ hφ
  have hf : f.val ∈ Submodule.span ℂ (gaussianGodementSections ν d ds) := by
    rw [hSpan]
    exact f.2
  obtain ⟨v₀, hv₀, hv₀eq⟩ := hT hf
  change J v₀ ∈ S at hv₀
  have he : v₀ = f := Subtype.ext hv₀eq
  exact he ▸ hv₀

private theorem canonicalAdjacentPolynomial_parameter (D : ComplexQuotientMeasureData r)
    (a : ℂˣ) (l : L) (k : Fin m → ℤ) (q : Q) (V : H → ℂ)
    (hV : V ∈ complexWhittakerModel r (characterList k q) a)
    (p : ℂ → P) (hp : Differentiable ℂ p)
    (hInit : ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball 0 δ,
      HasCanonicalAdjacentPolynomial D a l (p z) (characterList k q) V) :
    HasCanonicalAdjacentPolynomial D a l (p 1) (characterList k q) V := by
  intro f
  let μ := complexSelfDualMeasure a
  let es := characterList k q
  let W (z : ℂ) := continuedJacquet μ a l (p z) (transferProfile l (p 1) (p z) f)
  let F (z s : ℂ) := (complexPairLFactor (characterList l (p z)) es).denominator s *
    complexUnequalIntegral gap D (W z) V s
  let S := ball (0 : ℂ) 3
  obtain ⟨σ, hConv, hZ, _⟩ := complexUnequalCanonicalFamily gap μ a D l (p 1) f p hp es V hV 3
  change DifferentiableOn ℂ (fun u : ℂ × ℂ => complexUnequalIntegral gap D (W u.1) V u.2)
    (S ×ˢ {s : ℂ | σ < s.re}) at hZ
  have hF (s : ℂ) (hs : σ < s.re) : DifferentiableOn ℂ (fun z => F z s) S := by
    have hL := differentiable_pairDenominator l k p (fun _ => q) hp (differentiable_const q)
      (fun _ => s) (differentiable_const s)
    have hE : Differentiable ℂ (fun z : ℂ => (z, s)) :=
      differentiable_id.prodMk (differentiable_const s)
    have hm : MapsTo (fun z : ℂ => (z, s)) S (S ×ˢ {s : ℂ | σ < s.re}) := fun z hz => ⟨hz, hs⟩
    have hR := hZ.comp hE.differentiableOn hm
    exact hL.differentiableOn.mul hR
  obtain ⟨δ, hδ, hδ'⟩ := hInit
  let U := ball (0 : ℂ) (min δ 3)
  have hUS : U ⊆ S := ball_subset_ball (min_le_right _ _)
  have hPoly (z : ℂ) (hz : z ∈ U) :
      ∃ R : Polynomial ℂ, ∀ s : ℂ, σ < s.re → F z s = R.eval s := by
    have hw := hδ' z (ball_subset_ball (min_le_left _ _) hz) (transferProfile l (p 1) (p z) f)
    obtain ⟨R, τ, hR⟩ := hw
    let D₀ := (complexPairLFactor (characterList l (p z)) es).denominator
    have hHol : DifferentiableOn ℂ (F z) {s : ℂ | σ < s.re} := by
      have hL := (complexPairLFactor (characterList l (p z)) es).entire
      have hE : Differentiable ℂ (fun s : ℂ => (z, s)) := (differentiable_const z).prodMk differentiable_id
      have hm : MapsTo (fun s : ℂ => (z, s)) {s : ℂ | σ < s.re} (S ×ˢ {s : ℂ | σ < s.re}) :=
        fun s hs => ⟨hUS hz, hs⟩
      have hY := hZ.comp hE.differentiableOn hm
      exact hL.differentiableOn.mul hY
    obtain ⟨b, hb⟩ := complexPairLFactor_denominator_ne_zero (characterList l (p z)) es
    refine ⟨R, fun s hs => eqOn_halfPlane hHol R.differentiable.differentiableOn
      (σ₁ := max τ b) (fun t ht => ?_) hs⟩
    have ht' := (le_max_left τ b).trans_lt ht
    have ht₀ := hb t ((le_max_right τ b).trans_lt ht)
    have hEq : complexUnequalIntegral gap D (W z) V t = R.eval t * (D₀ t)⁻¹ := (hR t ht').2
    change D₀ t * complexUnequalIntegral gap D (W z) V t = _
    rw [hEq]
    rw [mul_left_comm, mul_inv_cancel₀ ht₀, mul_one]
  obtain ⟨_, hR⟩ := polynomialFiberContinuation S U isOpen_ball (convex_ball _ _).isPreconnected isOpen_ball
    ⟨0, mem_ball_self (lt_min hδ (by norm_num))⟩ hUS σ F hF hPoly
  have hOne : (1 : ℂ) ∈ S := by simp [S, Metric.mem_ball, dist_zero_right]
  obtain ⟨R, _, hR₁⟩ := hR 1 hOne
  obtain ⟨b, hb⟩ := complexPairLFactor_denominator_ne_zero (characterList l (p 1)) es
  change complexUnequalIntegrand gap (continuedJacquet μ a l (p 1) f) V ∈ _
  rw [← transferProfile_self l (p 1) f]
  refine ⟨R, max σ b, fun s hs => ⟨(hConv 1 hOne s ((le_max_left _ _).trans_lt hs)).1, ?_⟩⟩
  have he := hR₁ s ((le_max_left _ _).trans_lt hs)
  have hne := hb s ((le_max_right _ _).trans_lt hs)
  change complexUnequalIntegral gap D (W 1) V s = _
  rw [← he]
  change _ = ((complexPairLFactor (characterList l (p 1)) es).denominator s *
    complexUnequalIntegral gap D (W 1) V s) * ((complexPairLFactor (characterList l (p 1)) es).denominator s)⁻¹
  rw [mul_comm ((complexPairLFactor (characterList l (p 1)) es).denominator s),
    mul_assoc, mul_inv_cancel₀ hne, mul_one]

/-- At a trace scale of unit modulus, lower equal-rank polynomial Gaussian normalization
implies polynomial normalization for every adjacent ordinary test. -/
def ComplexOrdinaryAdjacentPolynomialStatement : Prop :=
  ∀ (r : ℕ) (a : ℂˣ), ‖(a : ℂ)‖ = 1 →
    ComplexEqualPolynomialAtRank r a → ComplexAdjacentPolynomialAtRank r a

set_option maxHeartbeats 1500000 in
theorem complexOrdinaryAdjacentPolynomial : ComplexOrdinaryAdjacentPolynomialStatement := by
  intro r a ha hEqual ds es hds hes D W V
  obtain ⟨l, p, rfl⟩ := exists_characterList ds hds
  obtain ⟨k, q, rfl⟩ := exists_characterList es hes
  let μ := complexSelfDualMeasure (-a)
  let B := continuedJacquet μ (-a) l p
  have hB : complexWhittakerModel (r + 1) (characterList l p) a = B.range := by
    simpa only [neg_neg] using (complexJacquetMultiplicityOne (r + 1) μ (-a) l p).2
  let C' := continuedJacquet μ a k q
  have hC : complexWhittakerModel r (characterList k q) (-a) = C'.range :=
    (complexJacquetMultiplicityOne r μ a k q).2
  have hW : W.val ∈ B.range :=
    (congrArg (fun S : Submodule ℂ _ => W.val ∈ S) hB).mp W.2
  have hV : V.val ∈ C'.range :=
    (congrArg (fun S : Submodule ℂ _ => V.val ∈ S) hC).mp V.2
  obtain ⟨f, hf⟩ := hW
  obtain ⟨v, hv⟩ := hV
  have hvModel : C' v ∈ complexWhittakerModel r (characterList k q) (-a) := by
    rw [hC]
    exact ⟨v, rfl⟩
  have hAll : ∀ p₀ : Fin (r + 1 + 1) → ℂ,
      HasCanonicalAdjacentPolynomial D (-a) l p₀ (characterList k q) (C' v) := by
    apply canonicalChamberRemoval
    · exact canonicalAdjacentPolynomial_parameter D (-a) l k q (C' v) hvModel
    · intro q₀
      exact canonicalAdjacentPolynomial_chamber D (-a) (by simpa using ha)
        (by simpa only [neg_neg] using hEqual) l q₀ _ C' (complexJacquetIntertwiner r μ a k q) v
  have hKernel := hAll p f
  change complexUnequalIntegrand (Nat.lt_succ_self r) (B f) (C' v) ∈ _ at hKernel
  rw [hf, hv] at hKernel
  exact exists_ordinaryPolynomialNormalization_of_mem hKernel

end Langlands.Global.RankinSelbergGlobal
