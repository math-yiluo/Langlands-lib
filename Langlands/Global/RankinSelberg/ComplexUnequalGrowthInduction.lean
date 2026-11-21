import Langlands.Global.RankinSelberg.ArchimedeanStripGrowth
import Langlands.Global.RankinSelberg.ComplexAdjacentCanonical
import Langlands.Global.RankinSelberg.ComplexAdjacentFromEqualGrowth
import Langlands.Global.RankinSelberg.ComplexLocalEqualGrowthReduction
import Langlands.Global.RankinSelberg.ComplexLocalEqualGrowthStep
import Langlands.Global.RankinSelberg.ComplexLocalEqualRankZeroGrowth
import Langlands.Global.RankinSelberg.ComplexLocalUnequalFromNormalized

/-! # The unequal-rank induction with strip growth for every trace parameter -/

noncomputable section

open MeasureTheory
open scoped NNReal SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.LocalFactor.Archimedean
open ArchimedeanLocal
open ArchimedeanInverseMellin (StripExpType)
open ComplexAdjacentUnfolding (HasAdjacentLowerEqualGrowthInputs complexAdjacentCanonicalGrowth
  complexFourierTransform_splitRowTransform splitRowTransform)
open ComplexCompactProfileFamily (characterList)
open ComplexJacquet (HasComplexPairNormalizedGrowth ComplexLocalEqualGrowthAtRank ComplexLocalEqualStandardGrowthStatement
  complexLocalEqualRankZeroGrowth)
open ComplexJacquetContinuation (continuedJacquet complexJacquetIntertwiner ComplexJacquetIdentityProportionality
  complexLocalEqualGrowthStep)
open ComplexJacquetMultiplicityOne (complexJacquetMultiplicityOne exists_characterList)
open ComplexCharacterChange (centralCharacter amplitude amplitude_cpow primalMultiplier dualMultiplier
  differentiable_primalMultiplier differentiable_dualMultiplier changeQuotientMeasure normalizeWhittaker
  normalizeWhittaker_mem normalizeWhittaker_neg_mem primal_comparison dual_comparison
  epsilon_mul_primal_eq_dual_mul_standard)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

local notation "G" => fun n => Langlands.GeneralLinear n ℂ

private theorem standardEqualGrowth : ∀ r, ComplexLocalEqualGrowthAtRank r := by
  have hId : ComplexJacquetIdentityProportionality := by
    intro r μ a l p B hB
    obtain ⟨c, hc⟩ := (complexJacquetMultiplicityOne r μ a l p).1 B hB
    exact ⟨c, fun f => congrArg (fun T => T f 1) hc⟩
  intro r
  induction r with
  | zero => exact complexLocalEqualRankZeroGrowth
  | succ r ih =>
    exact complexLocalEqualGrowthStep hId (complexAdjacentFromEqualGrowth r ih)

private theorem stripExpType_amplitude_affine (a : ℂˣ) (c b : ℝ) :
    StripExpType (fun s => amplitude a ((c : ℂ) * s + (b : ℂ))) :=
  (((StripExpType.ofReal_cpow (norm_pos_iff.mpr a.ne_zero)).comp_add (b : ℂ)).comp_ofReal_mul c).congr
    (fun s => (amplitude_cpow a ((c : ℂ) * s + (b : ℂ))).symm)

private theorem primalMultiplier_stripExpType (r : ℕ) (a : ℂˣ) : StripExpType (primalMultiplier r a) := by
  refine (stripExpType_amplitude_affine a (-(r : ℝ) * (r + 1)) 0).congr fun s => ?_
  unfold primalMultiplier
  congr 1
  push_cast
  ring

private theorem dualMultiplier_stripExpType (r : ℕ) (ds es : List ComplexCharacterData) (a : ℂˣ) :
    StripExpType (dualMultiplier r ds es a) := by
  let c := ((centralCharacter ds a : ℂ) * (centralCharacter es a : ℂ)) ^ (r + 1)
  refine ((StripExpType.const c).mul (stripExpType_amplitude_affine a (-((r : ℝ) + 1) * (r + 2)) (r + 1))).congr fun s => ?_
  unfold dualMultiplier
  congr 2
  push_cast
  ring

/-- The equal-rank normalized equation with growth at one trace parameter transfers to any nonzero scale. -/
theorem complexEqualGrowth_scaled (r : ℕ) (hStd : ComplexLocalEqualGrowthAtRank r)
    (ds es : List ComplexCharacterData) (hds : ds.length = r + 1) (hes : es.length = r + 1)
    (a : ℂˣ) (D : ComplexQuotientMeasureData r) (W V : G (r + 1) → ℂ)
    (Φ : 𝓢((Fin (r + 1) → ℂ), ℂ)) (hW : W ∈ complexWhittakerModel r ds a)
    (hV : V ∈ complexWhittakerModel r es (-a)) :
    HasComplexPairNormalizedGrowth ds es a (complexCentralSign es ^ r)
      (complexEqualIntegral D W V Φ) (complexEqualDualIntegral a D W V Φ) := by
  let P := primalMultiplier r a
  let Pd := dualMultiplier r ds es a
  obtain ⟨N, Nd, hN, hNd, hNt, hNdt, ⟨σ, hR⟩, hFE⟩ :=
    hStd ds es hds hes (changeQuotientMeasure a D) (normalizeWhittaker a W) (normalizeWhittaker a V)
      Φ (normalizeWhittaker_mem hW) (normalizeWhittaker_neg_mem hV)
  have hPt := (primalMultiplier_stripExpType r a).hasStripExponentialGrowth
  have hPdt := (dualMultiplier_stripExpType r ds es a).hasStripExponentialGrowth
  refine ⟨fun s => P s * N s, fun s => Pd s * Nd s,
    (differentiable_primalMultiplier r a).mul hN, (differentiable_dualMultiplier r ds es a).mul hNd,
    hPt.mul hNt, hPdt.mul hNdt, ⟨σ, fun s hs => ?_⟩, ?_⟩
  · obtain ⟨hP, hPd⟩ := hR s hs
    change (P s * N s = _) ∧ (Pd s * Nd s = _)
    rw [(primal_comparison hW hV D Φ s).2, (dual_comparison hds hes hW hV D Φ s).2, hP, hPd]
    change (_ * (_ * _) = _ * (P s * _)) ∧ (_ * (_ * _) = _ * (Pd s * _))
    constructor <;> ring
  · intro s
    let E := (complexPairEpsilon ds es a ‖(a : ℂ)‖₊ (nnnorm_pos.mpr a.ne_zero) s : ℂ)
    let E₁ := (complexPairEpsilon ds es 1 ‖((1 : ℂˣ) : ℂ)‖₊ (nnnorm_pos.mpr (1 : ℂˣ).ne_zero) s : ℂ)
    let c := complexCentralSign es ^ r
    change Pd (1 - s) * Nd (1 - s) = c * E * (P s * N s)
    rw [show Nd (1 - s) = c * E₁ * N s from hFE s]
    have hscale : E * P s = Pd (1 - s) * E₁ := epsilon_mul_primal_eq_dual_mul_standard hds hes a s
    calc
      _ = c * (Pd (1 - s) * E₁) * N s := by ring
      _ = _ := by rw [← hscale]; ring

/-- The entire normalized reflection with strip bounds on the finite Whittaker models at two ranks. -/
def ComplexLocalUnequalGrowthAtRanks (r t : ℕ) (h : t < r) : Prop :=
  ∀ (ds es : List ComplexCharacterData), ds.length = r + 1 → es.length = t + 1 →
  ∀ (a : ℂˣ) (D : ComplexQuotientMeasureData t) (W : G (r + 1) → ℂ) (V : G (t + 1) → ℂ),
    W ∈ complexWhittakerModel r ds a → V ∈ complexWhittakerModel t es (-a) →
    HasComplexPairNormalizedGrowth ds es a (complexCentralSign es ^ r)
      (complexUnequalIntegral h D W V) (complexUnequalDualIntegral h a D W V)

/-- The adjacent-rank normalized growth base holds for every nonzero trace parameter. -/
theorem complexUnequalAdjacentGrowth (r : ℕ) : ComplexLocalUnequalGrowthAtRanks (r + 1) r (Nat.lt_succ_self r) := by
  intro ds es hd he a D W V hW hV
  obtain ⟨l, p, rfl⟩ := exists_characterList ds hd
  obtain ⟨k, q, rfl⟩ := exists_characterList es he
  let μ := complexSelfDualMeasure (-a)
  have hL : complexWhittakerModel (r + 1) (characterList l p) a =
      LinearMap.range (continuedJacquet μ (-a) l p) := by
    simpa only [neg_neg] using (complexJacquetMultiplicityOne (r + 1) μ (-a) l p).2
  rw [hL] at hW
  rw [(complexJacquetMultiplicityOne r μ a k q).2] at hV
  obtain ⟨f, rfl⟩ := hW
  obtain ⟨v, rfl⟩ := hV
  have hLower (e : Fin (r + 1) → ℂ) :
      HasAdjacentLowerEqualGrowthInputs D (characterList (ComplexGodement.smallerWeights l) e)
        (characterList k q) (-a) := by
    intro U V hV φ
    let Φ := splitRowTransform (-a) φ
    have hU : U.val ∈ complexWhittakerModel r (characterList (ComplexGodement.smallerWeights l) e) a := by
      simpa only [neg_neg] using U.2
    have hF : complexFourierTransform a Φ = φ := by
      simpa only [Φ, neg_neg] using funext (complexFourierTransform_splitRowTransform (-a) φ)
    obtain ⟨σ, hσ⟩ := complexLocalEqualPairConvergence List.length_ofFn List.length_ofFn D U.val V Φ hU hV
    refine ⟨⟨σ, fun s hs => ⟨(hσ s hs).1, ?_⟩⟩, ?_⟩
    · simpa only [hF] using (hσ s hs).2
    · simpa only [Φ, neg_neg, characterList] using
        complexEqualGrowth_scaled r (standardEqualGrowth r) _ _ List.length_ofFn List.length_ofFn a D U.val V Φ hU hV
  have hg := complexAdjacentCanonicalGrowth D l k q (-a) hLower (continuedJacquet μ a k q)
    (complexJacquetIntertwiner r μ a k q) v p f
  simpa only [neg_neg] using hg

/-- The induction step beyond adjacent ranks. -/
def ComplexUnequalGrowthGapStep : Prop :=
  ∀ (r t : ℕ) (h : t < r), ComplexLocalUnequalGrowthAtRanks r t h →
    ComplexLocalUnequalGrowthAtRanks (r + 1) t (Nat.lt_succ_of_lt h)

/-- The remaining gap step suffices for the exact published unequal-rank theorem. -/
def ComplexUnequalGrowthInductionStatement : Prop :=
  ComplexUnequalGrowthGapStep → ComplexLocalUnequalFunctionalEquationStatement

theorem complexUnequalGrowth_all (hGap : ComplexUnequalGrowthGapStep) (r t : ℕ) (h : t < r) :
    ComplexLocalUnequalGrowthAtRanks r t h := by
  induction r generalizing t with
  | zero => exact (Nat.not_lt_zero _ h).elim
  | succ r ih =>
    rcases (Nat.lt_succ_iff.mp h).eq_or_lt with h' | h'
    · subst t
      exact complexUnequalAdjacentGrowth r
    · exact hGap r t h' (ih t h')

theorem complexUnequalGrowthInduction : ComplexUnequalGrowthInductionStatement := by
  intro hGap
  apply complexLocalUnequalFromNormalized
  intro r t h ds es hd he a D B B' hB hB' f f'
  have hW : B f ∈ complexWhittakerModel r ds a :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)
  have hV : B' f' ∈ complexWhittakerModel t es (-a) :=
    Submodule.mem_iSup_of_mem B' (Submodule.mem_iSup_of_mem hB' ⟨f', rfl⟩)
  obtain ⟨N, Nd, hN, hNd, _, _, ⟨σ, hEq⟩, hFE⟩ :=
    complexUnequalGrowth_all hGap r t h ds es hd he a D (B f) (B' f') hW hV
  exact ⟨σ, N, Nd, hN, hNd, hEq, hFE⟩

end Langlands.Global.RankinSelbergGlobal
