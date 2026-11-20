import Langlands.Global.Factors.CuspidalPairAbsoluteConvergenceProof
import Langlands.Global.Factors.CuspidalPairPoleStatement

/-! # Pair logarithmic series and the boundary limit for trace independence -/

noncomputable section

set_option autoImplicit false

universe u uQ

open Filter Topology

namespace Langlands.Global

open NumberField
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation OperatorRealization)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents residueCardinality)
open CuspidalPairAbsoluteConvergence CuspidalPairPoles
open Langlands.ClassField.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

/-- The pair logarithmic asymptotic of Jacquet–Shalika II, Theorem 4.1, in one
field. The imaginary shift records the unitary phase removed by the split-centre
normalization. -/
def CuspidalPairLogAsymptoticsAt (F : Type u) [Field F] [NumberField F]
    [CompactSpace (AdeleQuotient F)] : Prop :=
  ∀ (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    HasUnitaryCentralCharacter T → HasUnitaryCentralCharacter T' →
    IsTrivialOnSplitCentre T → IsTrivialOnSplitCentre T' →
    ∀ (P : CuspidalSpectralPresentation.{u, uQ} T) (P' : CuspidalSpectralPresentation.{u, uQ} T'),
    HasIrreducibleAdmissibleComponents P → HasIrreducibleAdmissibleComponents P' →
    ∀ (S : Finset (FinitePlace F)) (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S) (θ : ℝ),
      let selfPair := θ = 0 ∧ ∃ hrt : r = t,
        OperatorRealization.IsContragredientOf (n := t + 1) (hrt ▸ T.realization) T'.realization
      let normalizedLogSeries (σ : ℝ) :=
        (∑' x : {v : FinitePlace F // v ∉ S} × ℕ,
          logEulerTerm P P' hP hP' x.1 x.2 ((σ : ℂ) + θ * Complex.I)) /
          (Real.log (1 / (σ - 1)) : ℂ)
      (selfPair → Tendsto normalizedLogSeries (𝓝[>] 1) (𝓝 1)) ∧
        (¬ selfPair → Tendsto normalizedLogSeries (𝓝[>] 1) (𝓝 0))

namespace PairLogAsymptotics

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- The terms of the double series decrease with the real part. -/
theorem norm_logEulerTerm_le_of_le_re {r t : ℕ} {T : CuspidalOperatorRealization F r}
    {T' : CuspidalOperatorRealization F t} (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T') {S : Finset (FinitePlace F)}
    (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (x : {v : FinitePlace F // v ∉ S} × ℕ) {s : ℂ} {σ : ℝ} (hσ : σ ≤ s.re) :
    ‖logEulerTerm P P' hP hP' x.1 x.2 s‖ ≤ ‖logEulerTerm P P' hP hP' x.1 x.2 (σ : ℂ)‖ := by
  rw [norm_logEulerTerm, norm_logEulerTerm, Complex.ofReal_re]
  have hl : 0 ≤ logExponent x := (Real.log_pos one_lt_two).le.trans (log_two_le_logExponent x)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith

/-- `log (1/(σ - 1)) → +∞` as `σ → 1⁺`. -/
theorem tendsto_log_inv_sub_one :
    Tendsto (fun σ : ℝ => Real.log (1 / (σ - 1))) (𝓝[>] 1) atTop := by
  have h1 : Tendsto (fun σ : ℝ => σ - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    have hc : Tendsto (fun σ : ℝ => σ - 1) (𝓝 1) (𝓝 0) := by
      have := (continuous_sub_right (1 : ℝ)).tendsto (1 : ℝ)
      simpa using this
    refine tendsto_nhdsWithin_iff.mpr ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact Set.mem_Ioi.mpr (sub_pos.mpr (Set.mem_Ioi.mp hσ))
  have h2 : Tendsto (fun σ : ℝ => 1 / (σ - 1)) (𝓝[>] 1) atTop := by
    have := tendsto_inv_nhdsGT_zero.comp h1
    simpa [Function.comp_def, one_div] using this
  exact Real.tendsto_log_atTop.comp h2

end PairLogAsymptotics

end Langlands.Global
