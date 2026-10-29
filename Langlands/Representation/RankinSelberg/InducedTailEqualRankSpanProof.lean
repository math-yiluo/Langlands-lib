import Langlands.Representation.RankinSelberg.InducedTailSpanStatement
import Langlands.Representation.Whittaker.TwoBlockExtensionProof
import Langlands.Representation.RankinSelberg.UnipotentQuotient
import Langlands.Representation.RankinSelberg.RationalContinuationLinearProof
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Equal-tail-rank induced Laurent-span inclusion

Transport actual convergent equal-rank zeta values through the published
two-block Whittaker extension and deduce the closed Laurent-span inclusion.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV₁ uV₂ uW

namespace InducedTailEqualRank

variable {F : Type uF} [Field F] [TopologicalSpace F]

omit [TopologicalSpace F] in
/-- The positive half-modulus cancels the unequal-rank spectral shift. -/
theorem halfModulus_weight (abv : AbsoluteValue F ℝ) {m : ℕ}
    (g : Langlands.GeneralLinear m F) (d : ℕ) (s : ℂ) :
    (Real.rpow (abv (Matrix.det g.val)) ((d : ℝ) / 2) : ℂ) *
      determinantWeight abv g (s - (d : ℂ) / 2) = determinantWeight abv g s := by
  unfold determinantWeight
  rw [Real.rpow_eq_pow,
    Complex.ofReal_cpow (abv.nonneg (Matrix.det g.val)) ((d : ℝ) / 2)]
  push_cast
  rw [← Complex.cpow_add _ _
    (Complex.ofReal_ne_zero.mpr (abv.ne_zero g.det_ne_zero))]
  congr 1
  ring

/-- A matching coefficient restriction gives equality of the actual quotient
integrands for every spectral parameter and every zero-row matrix. -/
theorem integrand_eq (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {n k : ℕ} (W : WhittakerFunctions ψ (n + (0 + k + 1)))
    (W₂ : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F))
    (hext : ∀ g : Langlands.GeneralLinear (n + 1) F,
      W.val (appendIdentity n (0 + k + 1) g) =
        W₂.val g * Φ (lastRow g) *
          (Real.rpow (abv (Matrix.det g.val)) (((0 + k + 1 : ℕ) : ℝ) / 2) : ℂ))
    (s : ℂ) (x : Matrix (Fin 0) (Fin (n + 1)) F)
    (q : LeftUnipotentQuotient n F) :
    unequalRankIntegrand ψ abv 0 k W W' s x q =
      equalRankIntegrand ψ abv W₂ W' Φ s q := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [unequalRankIntegrand_mk, unequalRankMatrix_zero_rows, hext,
      equalRankIntegrand_mk]
    calc
      _ = (W₂.val g * W'.val g * Φ (lastRow g)) *
          ((Real.rpow (abv (Matrix.det g.val))
            (((0 + k + 1 : ℕ) : ℝ) / 2) : ℂ) *
            determinantWeight abv g (s - ((0 + k + 1 : ℕ) : ℂ) / 2)) := by ring
      _ = _ := by rw [halfModulus_weight]

/-- Absolute convergence transfers to the product with the unit Dirac measure. -/
theorem converges (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {n k : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin 0) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (W : WhittakerFunctions ψ (n + (0 + k + 1)))
    (W₂ : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F))
    (hext : ∀ g : Langlands.GeneralLinear (n + 1) F,
      W.val (appendIdentity n (0 + k + 1) g) =
        W₂.val g * Φ (lastRow g) *
          (Real.rpow (abv (Matrix.det g.val)) (((0 + k + 1 : ℕ) : ℝ) / 2) : ℂ))
    (s : ℂ) (hc : EqualRankConverges ψ abv μ W₂ W' Φ s) :
    UnequalRankConverges ψ abv 0 k μ (Measure.dirac 0) W W' s := by
  unfold UnequalRankConverges
  simp_rw [integrand_eq ψ abv W W₂ W' Φ hext]
  exact hc.comp_fst (Measure.dirac 0)

/-- Equality of the total scalar integrals; convergence is supplied separately. -/
theorem integral_eq (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {n k : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin 0) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (W : WhittakerFunctions ψ (n + (0 + k + 1)))
    (W₂ : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F))
    (hext : ∀ g : Langlands.GeneralLinear (n + 1) F,
      W.val (appendIdentity n (0 + k + 1) g) =
        W₂.val g * Φ (lastRow g) *
          (Real.rpow (abv (Matrix.det g.val)) (((0 + k + 1 : ℕ) : ℝ) / 2) : ℂ))
    (s : ℂ) :
    unequalRankIntegral ψ abv 0 k μ (Measure.dirac 0) W W' s =
      equalRankIntegral ψ abv μ W₂ W' Φ s := by
  unfold unequalRankIntegral equalRankIntegral
  simp_rw [integrand_eq ψ abv W W₂ W' Φ hext]
  simp

omit [TopologicalSpace F] in
/-- Entry-preserving reindexing along reflexive rank equality is the identity. -/
theorem reindex_finCongr_self {m : ℕ} (h : m = m)
    (g : Langlands.GeneralLinear m F) :
    GeneralLinear.reindex (finCongr h) g = g := by
  rw [finCongr_refl]
  apply Units.ext
  rfl

omit [TopologicalSpace F] in
/-- Equal identity-block sizes give equal rank-transported embeddings. -/
theorem reindex_appendIdentity_congr {r n d d' : ℕ} (hd : d = d')
    (hr : n + d + 1 = r + 1) (hr' : n + d' + 1 = r + 1)
    (g : Langlands.GeneralLinear (n + 1) F) :
    GeneralLinear.reindex (finCongr hr) (appendIdentity n d g) =
      GeneralLinear.reindex (finCongr hr') (appendIdentity n d' g) := by
  subst d'
  rfl

/-- Transfer one convergent equal-rank rational zeta value through a specified
extension coefficient, retaining the explicit arithmetic rank transport. -/
theorem value_mem (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) {r n k : ℕ} (hr : r = n + (0 + k + 1))
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin 0) (Fin (n + 1)) F)]
    {V : Type uV₁} [AddCommGroup V] [Module ℂ V]
    {V' : Type uV₂} [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V')
    (μ : Measure (LeftUnipotentQuotient n F))
    (W : WhittakerFunctions ψ r) (hW : W ∈ whittakerSet ψ r π)
    (W₂ : WhittakerFunctions ψ n) (W' : InverseWhittakerFunctions ψ n)
    (hW' : W' ∈ inverseWhittakerSet ψ n σ)
    (Φ : SchwartzBruhat (Fin (n + 1) → F))
    (hext : ∀ g : Langlands.GeneralLinear (n + 1) F,
      W.val (GeneralLinear.reindex (finCongr (by omega))
        (appendIdentity n (0 + k + 1) g)) =
        W₂.val g * Φ (lastRow g) *
          (Real.rpow (abv (Matrix.det g.val)) (((0 + k + 1 : ℕ) : ℝ) / 2) : ℂ))
    (R : RationalFunctions)
    (hc : ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      EqualRankConverges ψ abv μ W₂ W' Φ s)
    (hR : HasRationalContinuation q (equalRankIntegral ψ abv μ W₂ W' Φ) R) :
    R ∈ unequalRankZetaValuesAt 0 k hr q ψ abv μ (Measure.dirac 0) π σ := by
  subst r
  simp_rw [reindex_finCongr_self] at hext
  change R ∈ unequalRankZetaValues q ψ abv 0 k μ (Measure.dirac 0) π σ
  refine ⟨W, hW, W', hW', ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hc
    exact ⟨a, fun s hs => converges ψ abv μ W W₂ W' Φ hext s (ha s hs)⟩
  · apply RationalContinuationLinear.continuation_of_eq_on_right hR
    exact ⟨0, fun s _ => integral_eq ψ abv μ W W₂ W' Φ hext s⟩

end InducedTailEqualRank

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- Assemble the equal-tail-rank span inclusion from an extension formula. -/
theorem inducedTailEqualRankSpan_of_extension
    (hext : TwoBlockWhittakerExtensionStatement.{uF, uV₁, uV₂}) :
    InducedTailEqualRankSpanStatement.{uF, uV₁, uV₂, uW} := by
  intro p hp F ψ ν a b t V₁ _ _ V₂ _ _ W _ _ π₁ π₂ σ hπ₁ hπ₂ hσ π₁' π₂' ξ h
  have ht : t = b := by omega
  subst t
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (b + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (b + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (b + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (b + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient b F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient b F.Carrier) := ⟨rfl⟩
  dsimp only
  intro _ _ μtail μfull htail hfull
  have hm : μfull = μtail :=
    (unipotentQuotientHaar_unique F.Carrier b μfull hfull).trans
      (unipotentQuotientHaar_unique F.Carrier b μtail htail).symm
  subst μfull
  have hk : a + 1 + b - b - 1 = a := by omega
  simp only [rectangularMeasure_zero_rows]
  apply zetaSpan_mono
  rintro R ⟨W₂, hW₂, W', hW', Φ, hc, hR⟩
  obtain ⟨Wfull, hWfull, hWg⟩ :=
    hext p F ψ a b π₁ π₂ hπ₁ hπ₂ W₂ hW₂ Φ
  exact InducedTailEqualRank.value_mem
    F.canonicalTopologicalData.residueCardinality ψ
    (normalizedAbsoluteValue F.canonicalTopologicalData)
    (r := a + 1 + b) (n := b) (k := a + 1 + b - b - 1) (by omega)
    ξ σ μtail Wfull hWfull W₂ W' hW' Φ
    (by
      intro g
      rw [InducedTailEqualRank.reindex_appendIdentity_congr
        (show 0 + (a + 1 + b - b - 1) + 1 = a + 1 by omega) _ (by omega)]
      simpa only [hk, Nat.zero_add, normalizedAbsoluteValue_apply] using hWg g) R hc hR

/-- The equal-tail-rank Laurent-span inclusion for canonical upper induction. -/
theorem inducedTailEqualRankSpan :
    InducedTailEqualRankSpanStatement.{uF, uV₁, uV₂, uW} :=
  inducedTailEqualRankSpan_of_extension.{uF, uV₁, uV₂, uW}
    twoBlockWhittakerExtension.{uF, uV₁, uV₂}

end Langlands.RankinSelberg
