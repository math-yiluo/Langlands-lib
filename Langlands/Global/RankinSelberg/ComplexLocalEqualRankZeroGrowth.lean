import Langlands.Global.RankinSelberg.ComplexLocalEqualRankZero
import Langlands.Global.RankinSelberg.ComplexLocalFourierSchwartz
import Langlands.Global.RankinSelberg.ComplexLocalNormalizedGrowth
import Langlands.Global.RankinSelberg.ComplexRankZeroStripGrowth

/-! # Exponential strip growth for the complex rank-zero equal pair -/

noncomputable section

open MeasureTheory
open Langlands.LocalFactor.Archimedean
open scoped SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal
open FunctionalEquationComparison.CompletedEquationAdapter (complexPairLFactor_denominator_ne_zero)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

local notation "I" => Fin (0 + 1)
local notation "G" => Langlands.GeneralLinear (0 + 1) ℂ
local notation "Test" => 𝓢((I → ℂ), ℂ)

private theorem rank_zero_trace_growth (D : ComplexQuotientMeasureData 0) (d e : ComplexCharacterData)
    (W V : G → ℂ) (C E : ℂ) (Φ : Test)
    (hW : ∀ g, W g = C * (d.character (GeneralLinear.determinant g) : ℂ))
    (hV : ∀ g, V g = E * (e.character (GeneralLinear.determinant g) : ℂ)) :
    ∃ N : ℂ → ℂ, Differentiable ℂ N ∧ HasStripExponentialGrowth N ∧
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        N s = (complexPairLFactor [d] [e]).denominator s * complexEqualIntegral D W V Φ s := by
  obtain ⟨N, hGrowth⟩ := ComplexRankZero.complexRankZeroStripGrowth D d e W V C E hW hV Φ
  obtain ⟨σ, hN⟩ := N.eq_on_right
  obtain ⟨τ, hτ⟩ := complexPairLFactor_denominator_ne_zero [d] [e]
  refine ⟨N.value, fun s => (N.analytic s (Set.mem_univ _)).differentiableAt, hGrowth,
    max σ τ, fun s hs => ?_⟩
  rw [hN s ((le_max_left _ _).trans_lt hs), mul_left_comm,
    mul_inv_cancel₀ (hτ s ((le_max_right _ _).trans_lt hs)), mul_one]

private theorem dual_rank_zero_scalar (d : ComplexCharacterData) {W : G → ℂ} {C : ℂ}
    (hW : ∀ g, W g = C * (d.character (GeneralLinear.determinant g) : ℂ)) (g : G) :
    ArchimedeanLocal.dualFunction (0 + 1) W g =
      C * (d.inv.character (GeneralLinear.determinant g) : ℂ) := by
  rw [ComplexRankZero.dualFunction_apply, hW, Langlands.RankinSelberg.RankOneGammaTwist.determinant_inverseTranspose,
    ComplexRankZero.character_inv_apply, ComplexCharacterData.inv_character_apply]

/-- The usual rank-zero equal pair, normalized by its Tate factors, has exponential
strip growth on both sides at the standard additive character. -/
def ComplexLocalEqualRankZeroGrowthStatement : Prop :=
  ∀ (ds es : List ComplexCharacterData), ds.length = 0 + 1 → es.length = 0 + 1 →
  ∀ (D : ComplexQuotientMeasureData 0) (W V : G → ℂ) (Φ : Test),
    W ∈ complexWhittakerModel 0 ds 1 → V ∈ complexWhittakerModel 0 es (-1) →
    HasComplexPairNormalizedGrowth ds es 1 (complexCentralSign es ^ (0 : ℕ))
      (complexEqualIntegral D W V Φ) (complexEqualDualIntegral 1 D W V Φ)

set_option maxHeartbeats 900000 in
theorem complexLocalEqualRankZeroGrowth : ComplexLocalEqualRankZeroGrowthStatement := by
  intro ds es hd he D W V Φ hW hV
  obtain ⟨d, rfl⟩ := List.length_eq_one_iff.mp hd
  obtain ⟨e, rfl⟩ := List.length_eq_one_iff.mp he
  obtain ⟨C, hC⟩ := ComplexRankZero.exists_eq_of_mem_complexWhittakerModel hW
  obtain ⟨E, hE⟩ := ComplexRankZero.exists_eq_of_mem_complexWhittakerModel hV
  obtain ⟨Ψ, hΨ⟩ := exists_schwartz_complexFourierTransform 1 Φ
  obtain ⟨N, hN, hNg, ρ, hρ⟩ := rank_zero_trace_growth D d e W V C E Φ hC hE
  obtain ⟨Nd, hNd, hNdg, ρd, hρd⟩ := rank_zero_trace_growth D d.inv e.inv
    (ArchimedeanLocal.dualFunction (0 + 1) W) (ArchimedeanLocal.dualFunction (0 + 1) V)
    C E Ψ (dual_rank_zero_scalar d hC) (dual_rank_zero_scalar e hE)
  have ht (s : ℂ) (hs : ρd < s.re) :
      Nd s = (complexPairLFactor [d.inv] [e.inv]).denominator s * complexEqualDualIntegral 1 D W V Φ s := by
    simpa only [hΨ, complexEqualIntegral, complexEqualDualIntegral] using hρd s hs
  obtain ⟨σ, M, Md, _, _, _, _, hM, hMd, hR, hRd, hFE⟩ :=
    complexLocalEqualRankZero [d] [e] hd he 1 D W V Φ hW hV
  refine ⟨N, Nd, hN, hNd, hNg, hNdg, ⟨max ρ ρd, fun s hs => ?_⟩, ?_⟩
  · exact ⟨hρ s ((le_max_left _ _).trans_lt hs), ht s ((le_max_right _ _).trans_lt hs)⟩
  · apply normalizedEquation_of_pairMeromorphicEquation
      (fun s => hM s (Set.mem_univ _)) (fun s => hMd s (Set.mem_univ _)) hFE hN hNd
    · simp_rw [complexPairEpsilon_one]
      exact continuous_const
    · intro s (hs : max σ (max ρ ρd) < s.re)
      have hσ := (le_max_left σ (max ρ ρd)).trans_lt hs
      have hρv := (le_max_left ρ ρd).trans_lt ((le_max_right σ _).trans_lt hs)
      have hρdv := (le_max_right ρ ρd).trans_lt ((le_max_right σ _).trans_lt hs)
      exact ⟨(hρ s hρv).trans (congrArg (_ * ·) (hR s hσ)),
        (ht s hρdv).trans (congrArg (_ * ·) (hRd s hσ))⟩

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
