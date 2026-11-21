import Langlands.Global.RankinSelberg.ComplexLocalEqualRankZero
import Langlands.Global.RankinSelberg.ComplexLocalFourierSchwartz
import Langlands.Global.RankinSelberg.ComplexLocalNormalizedGrowth
import Langlands.Global.RankinSelberg.ComplexTateProductStripGrowth

/-! # Exponential strip growth for the complex rank-zero equal pair -/

noncomputable section

open MeasureTheory
open Langlands.LocalFactor.Archimedean
open scoped SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal
open ComplexRankZero (lineSchwartz lineSchwartz_apply equalIntegral_eq complexPairLFactor_singleton)
open ComplexTateProduct (affineParameter normalizedZeta gammaNormalizer additiveWeight
  complexTateProductEntireFamily complexTateProductStripGrowth)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

local notation "I" => Fin (0 + 1)
local notation "G" => Langlands.GeneralLinear (0 + 1) ℂ
local notation "Test" => 𝓢((I → ℂ), ℂ)

private local instance : Unique I := inferInstanceAs (Unique (Fin 1))

private theorem zeta_on_single_coordinate (Φ : Test) (w : ℤ) (t s : ℂ) :
    ComplexRankZero.ComplexTate.zeta (lineSchwartz Φ) w t s =
      2 * ComplexTateProduct.zeta Φ (fun _ => w) (fun _ => s + t) := by
  rw [ComplexRankZero.ComplexTate.zeta, ComplexRankZero.ComplexTate.integral_two_smul, ComplexTateProduct.zeta]
  congr 1
  let f := ComplexTateProduct.integrand (Φ : (I → ℂ) → ℂ) (fun _ => w) (fun _ => s + t)
  have he := (volume_preserving_funUnique I ℂ).symm.integral_comp' f
  rw [← he]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  change ComplexRankZero.ComplexTate.integrand (lineSchwartz Φ) w t s z = f (fun _ => z)
  by_cases hz : z = 0 <;>
    simp [f, ComplexTateProduct.integrand, ComplexRankZero.ComplexTate.integrand, additiveWeight,
      lineSchwartz_apply, hz, mul_assoc]

private theorem stripGrowth_mul_const_left {f : ℂ → ℂ} (hf : HasStripExponentialGrowth f) (c : ℂ) :
    HasStripExponentialGrowth (fun s => c * f s) := by
  intro a b
  obtain ⟨C, K, T, hC, hK, h⟩ := hf a b
  refine ⟨‖c‖ * C, K, T, mul_nonneg (norm_nonneg _) hC, hK, fun s ha hb ht => ?_⟩
  rw [norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h s ha hb ht) (norm_nonneg _)

private theorem rank_zero_trace_growth (D : ComplexQuotientMeasureData 0) (d e : ComplexCharacterData)
    (W V : G → ℂ) (C E : ℂ) (Φ : Test)
    (hW : ∀ g, W g = C * (d.character (GeneralLinear.determinant g) : ℂ))
    (hV : ∀ g, V g = E * (e.character (GeneralLinear.determinant g) : ℂ)) :
    ∃ N : ℂ → ℂ, Differentiable ℂ N ∧ HasStripExponentialGrowth N ∧
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        N s = (complexPairLFactor [d] [e]).denominator s * complexEqualIntegral D W V Φ s := by
  obtain ⟨κ, _, hκ⟩ := ComplexRankZero.exists_measure_eq D
  let c : ℂ := (κ : ℂ) * (C * E)
  let w := (d.mul e).weight
  let t := (d.mul e).exponent
  have hZ (s : ℂ) : complexEqualIntegral D W V Φ s =
      c * ComplexTateProduct.zeta Φ (fun _ => w) (fun _ => s + t) := by
    rw [equalIntegral_eq d e hκ hW hV, zeta_on_single_coordinate]
    dsimp only [c, w, t]
    ring
  obtain ⟨H, hH⟩ := complexTateProductEntireFamily 0
  let N (s : ℂ) := c * H Φ (fun _ => w) (fun _ => s + t)
  have hAffine (s : ℂ) : affineParameter (fun _ : I => t) (fun _ => 1) s = fun _ => s + t := by
    funext j
    simp [affineParameter, add_comm t]
  have hN : Differentiable ℂ N := by
    simpa only [N, hAffine] using
      (hH.1 Φ (fun _ => w) (fun _ => t) (fun _ => 1)).const_mul c
  have hNg : HasStripExponentialGrowth N := by
    simpa only [N, hAffine] using stripGrowth_mul_const_left
      (complexTateProductStripGrowth 0 H hH Φ (fun _ => w) (fun _ => t) (fun _ => 1)) c
  refine ⟨N, hN, hNg, |t.re|, fun s hs => ?_⟩
  have hPos : 0 < (s + t).re := by rw [Complex.add_re]; linarith [neg_abs_le t.re]
  dsimp only [N]
  rw [hH.2 _ _ _ (fun _ => hPos), hZ, complexPairLFactor_singleton, normalizedZeta]
  rw [show (∏ _ : I, gammaNormalizer w (s + t)) = gammaNormalizer w (s + t) from
    Fin.prod_univ_one (fun _ : Fin 1 => gammaNormalizer w (s + t))]
  simp only [gammaNormalizer, w, t, add_assoc]
  ring

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
