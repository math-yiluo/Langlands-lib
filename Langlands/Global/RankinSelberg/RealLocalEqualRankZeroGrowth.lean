import Langlands.Global.RankinSelberg.RealLocalNormalizedGrowth
import Langlands.Global.RankinSelberg.RealRankZeroStripGrowth
import Langlands.Global.RankinSelberg.RealRankZeroLocal
import Langlands.Global.RankinSelberg.RankOneOrdinaryNormalizedTests
import Langlands.Global.RankinSelberg.RealFourierSchwartz
import Langlands.LocalFactor.RealBlockRankOne
import Langlands.LocalFactor.Archimedean.RealTateProof
import Langlands.Representation.RankinSelberg.RankOneGammaTwistAlgebra

/-! # The real rank-zero equal pair in normalized-growth form -/

noncomputable section

open Filter Set
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean
open scoped NNReal SchwartzMap

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open ArchimedeanLocal

private theorem dual_rankZero_scalar (c : RealCharacterData)
    {W : Langlands.GeneralLinear (0 + 1) ℝ → ℂ} {C : ℂ}
    (hW : ∀ g, W g = C * (c.character (GeneralLinear.determinant g) : ℂ))
    (g : Langlands.GeneralLinear (0 + 1) ℝ) :
    ArchimedeanLocal.dualFunction (0 + 1) W g =
      C * (c.inverse.character (GeneralLinear.determinant g) : ℂ) := by
  rw [RealRankZero.dualFunction_apply, hW,
    Langlands.RankinSelberg.RankOneGammaTwist.determinant_inverseTranspose,
    RealRankZero.character_inv_apply]
  show _ = C * (((c.character (GeneralLinear.determinant g))⁻¹ : ℂˣ) : ℂ)
  rw [Units.val_inv_eq_inv_val]

private theorem realPairEpsilon_scale_congr (ds es : List RealBlock) (b : ℝˣ) {c c' : ℝ≥0}
    (h : c = c') (hc : 0 < c) (hc' : 0 < c') (s : ℂ) :
    realPairEpsilon ds es b c hc s = realPairEpsilon ds es b c' hc' s := by
  subst h
  rfl

/-- The real rank-zero equal pair, on the uniform coefficient spaces, has the entire
normalized form with exponential strip growth for the dual lists `ds.map dualBlock`,
`es.map dualBlock`, the Fourier and epsilon parameter `-a`, the scale `sqrt |a|`, and the
sign `det(ds, -1) ^ 0`. -/
def RealLocalEqualRankZeroGrowthStatement : Prop :=
  ∀ (ds es : List RealBlock), realRank ds = 0 + 1 → realRank es = 0 + 1 →
  ∀ (a : ℝˣ) (D : RealQuotientMeasureData 0) (W W' : Langlands.GeneralLinear (0 + 1) ℝ → ℂ)
    (Φ : SchwartzMap (Fin (0 + 1) → ℝ) ℂ),
    W ∈ realUniformWhittakerModel 0 ds a → W' ∈ realUniformWhittakerModel 0 es (-a) →
    HasRealPairNormalizedGrowth ds es (ds.map RealLocalJacquet.dualBlock)
      (es.map RealLocalJacquet.dualBlock) (-a) (NNReal.sqrt ‖(a : ℝ)‖₊)
      (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))
      ((RealJacquet.determinant ds (-1) : ℂ) ^ (0 : ℕ))
      (realEqualIntegral D W W' Φ) (realEqualDualIntegral (-a) D W W' Φ)

theorem realLocalEqualRankZeroGrowth : RealLocalEqualRankZeroGrowthStatement := by
  intro ds es hds hes a D W W' Φ hW hW'
  obtain ⟨c, rfl⟩ := RealRankZero.eq_singleton_of_realRank_eq_one hds
  obtain ⟨c', rfl⟩ := RealRankZero.eq_singleton_of_realRank_eq_one hes
  obtain ⟨C, hC⟩ :=
    RealRankZero.exists_eq_of_mem_realWhittakerModel (RealUniformWhittaker.model_le_model _ _ hW)
  obtain ⟨C', hC'⟩ :=
    RealRankZero.exists_eq_of_mem_realWhittakerModel (RealUniformWhittaker.model_le_model _ _ hW')
  obtain ⟨Ψ, hΨ⟩ := RealFourierSchwartz.exists_schwartz_eq (-a) Φ
  have hc₀ : 0 < NNReal.sqrt ‖(a : ℝ)‖₊ := NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)
  have hscale : NNReal.sqrt ‖((-a : ℝˣ) : ℝ)‖₊ = NNReal.sqrt ‖(a : ℝ)‖₊ := by
    rw [Units.val_neg, nnnorm_neg]
  -- the continuation package from the real Tate theory
  obtain ⟨σ, M, Md, -, -, -, -, hM, hMd, hIM, hIdMd, hFE⟩ :=
    RealRankZero.realEqual_rankZero RealTate.realArchimedeanTateStatement (-a) c c' c.inverse c'.inverse
      rfl (by change -c.exponent + -c'.exponent = -(c.exponent + c'.exponent); ring)
      D hC hC' Φ
  have hP : ContinuationPackage (realEqualIntegral D W W' Φ) (realEqualDualIntegral (-a) D W W' Φ)
      (fun s => ((realPairLFactor [.character c] [.character c']).denominator s)⁻¹)
      (fun s => ((realPairLFactor ([RealBlock.character c].map RealLocalJacquet.dualBlock)
        ([RealBlock.character c'].map RealLocalJacquet.dualBlock)).denominator s)⁻¹)
      (fun s => (realPairEpsilon [.character c] [.character c'] (-a) (NNReal.sqrt ‖(a : ℝ)‖₊)
        hc₀ s : ℂ))
      ((RealJacquet.determinant [.character c] (-1) : ℂ) ^ (0 : ℕ)) := by
    refine ⟨σ, M, Md, hM, hMd, hIM, hIdMd, ?_⟩
    filter_upwards [hFE] with s hs
    rw [pow_zero, one_mul, ← realPairEpsilon_scale_congr _ _ _ hscale]
    exact hs
  -- the two entire normalizations with strip growth
  obtain ⟨N, hNg⟩ := RealRankZero.realRankZeroStripGrowth D c c' W W' C C' hC hC' Φ
  obtain ⟨Nd, hNdg⟩ := RealRankZero.realRankZeroStripGrowth D c.inverse c'.inverse
    (ArchimedeanLocal.dualFunction (0 + 1) W) (ArchimedeanLocal.dualFunction (0 + 1) W') C C'
    (dual_rankZero_scalar c hC) (dual_rankZero_scalar c' hC') Ψ
  obtain ⟨ρ, hρ⟩ := N.eq_on_right
  obtain ⟨ρd, hρd⟩ := Nd.eq_on_right
  obtain ⟨τ, hτ⟩ := ArchimedeanRealPairFactor.realLFactor_ne_zero
    (realPairBlocks [.character c] [.character c'])
  obtain ⟨τd, hτd⟩ := ArchimedeanRealPairFactor.realLFactor_ne_zero
    (realPairBlocks [.character c.inverse] [.character c'.inverse])
  refine hasRealPairNormalizedGrowth_of_continuationPackage hP
    (fun s => (N.analytic s (mem_univ s)).differentiableAt)
    (fun s => (Nd.analytic s (mem_univ s)).differentiableAt) hNg hNdg
    (σ := max (max ρ ρd) (max τ τd)) fun s hs => ⟨?_, ?_⟩
  · have hP0 : (realPairLFactor [.character c] [.character c']).denominator s ≠ 0 :=
      hτ s (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hs)
    rw [hρ s (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hs)]
    field_simp
  · have hP0 : (realPairLFactor [.character c.inverse] [.character c'.inverse]).denominator s ≠ 0 :=
      hτd s (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hs)
    have h := hρd s (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hs)
    change Nd.value s = (realPairLFactor [.character c.inverse] [.character c'.inverse]).denominator s *
      realEqualIntegral D (ArchimedeanLocal.dualFunction (0 + 1) W)
        (ArchimedeanLocal.dualFunction (0 + 1) W') (realFourierTransform (-a) Φ) s
    rw [← hΨ]
    change realEqualIntegral D _ _ Ψ s = _ at h
    rw [h]
    field_simp

end Langlands.Global.RankinSelbergGlobal.RealJacquet
