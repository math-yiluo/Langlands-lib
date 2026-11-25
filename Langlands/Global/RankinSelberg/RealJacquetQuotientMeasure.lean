import Langlands.Analysis.Local.QuotientInvariantComparison
import Langlands.Global.RankinSelberg.RealJacquetConventionReduction

/-! # Compatible quotient measures in the real local equation packages -/

noncomputable section

open MeasureTheory TopologicalSpace
open scoped Matrix.Norms.Operator
open Langlands.LocalFactor.Archimedean
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

namespace RealJacquet

/-- Scaling both measures and both integrals by the same nonnegative real scalar
preserves the equation package with the same factors and sign. -/
theorem EquationPackage.smul_measures {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {K : ℂ → X → ℂ} {Kd : ℂ → Y → ℂ}
    {Z Zd L Ld E : ℂ → ℂ} {sign : ℂ}
    (h : EquationPackage μ ν K Kd Z Zd L Ld E sign) (c : ℝ) :
    EquationPackage (ENNReal.ofReal c • μ) (ENNReal.ofReal c • ν) K Kd
      (fun s => ((ENNReal.ofReal c).toReal : ℂ) * Z s)
      (fun s => ((ENNReal.ofReal c).toReal : ℂ) * Zd s) L Ld E sign := by
  obtain ⟨σ, M, Md, hK, hKd, hZ, hZd, hM, hMd, hZM, hZdMd, hFE⟩ := h
  let z : ℂ := (ENNReal.ofReal c).toReal
  refine ⟨σ, fun s => z * M s, fun s => z * Md s,
    fun s hs => (hK s hs).smul_measure ENNReal.ofReal_ne_top,
    fun s hs => (hKd s hs).smul_measure ENNReal.ofReal_ne_top,
    hZ.const_mul z, hZd.const_mul z, (MeromorphicOn.const z).mul hM,
    (MeromorphicOn.const z).mul hMd, fun s hs => congrArg (z * ·) (hZM s hs),
    fun s hs => congrArg (z * ·) (hZdMd s hs), ?_⟩
  filter_upwards [hFE] with s hs
  calc
    _ = z * (L s * Md (1 - s)) := by ring
    _ = z * (sign * E s * Ld (1 - s) * M s) := by rw [hs]
    _ = _ := by ring

end RealJacquet

open ArchimedeanLocal

private local instance (t : ℕ) : MeasurableSpace (Langlands.GeneralLinear (t + 1) ℝ) := borel _
private local instance (t : ℕ) : BorelSpace (Langlands.GeneralLinear (t + 1) ℝ) := ⟨rfl⟩
private local instance (t : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent (t + 1) ℝ) := borel _
private local instance (t : ℕ) : BorelSpace (GeneralLinear.upperUnipotent (t + 1) ℝ) := ⟨rfl⟩
private local instance (t : ℕ) : MeasurableSpace (RankinSelberg.LeftUnipotentQuotient t ℝ) := borel _
private local instance (t : ℕ) : BorelSpace (RankinSelberg.LeftUnipotentQuotient t ℝ) := ⟨rfl⟩

namespace RealJacquet

/-- Compatibility makes two real unipotent quotient measures positive multiples. -/
theorem quotientMeasure_eq_pos_smul {t : ℕ} (D D₀ : RealQuotientMeasureData t) :
    ∃ c : ℝ, 0 < c ∧ D.measure = ENNReal.ofReal c • D₀.measure := by
  let H := GeneralLinear.upperUnipotent (t + 1) ℝ
  have hH : IsClosed (H : Set (Langlands.GeneralLinear (t + 1) ℝ)) :=
    GeneralLinear.UpperUnipotent.isClosed
  let _ : LocallyCompactSpace (Matrix (Fin (t + 1)) (Fin (t + 1)) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin (t + 1) → Fin (t + 1) → ℝ))
  let _ : LocallyCompactSpace (Langlands.GeneralLinear (t + 1) ℝ) :=
    Units.isOpenEmbedding_val.locallyCompactSpace
  let _ : SecondCountableTopology (Langlands.GeneralLinear (t + 1) ℝ) :=
    Units.isOpenEmbedding_val.isInducing.secondCountableTopology
  let _ : PseudoMetrizableSpace (Langlands.GeneralLinear (t + 1) ℝ) :=
    Units.isOpenEmbedding_val.isInducing.pseudoMetrizableSpace
  let _ : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let _ : SigmaCompactSpace H := hH.isClosedEmbedding_subtypeVal.sigmaCompactSpace
  let _ : PseudoMetrizableSpace H :=
    hH.isClosedEmbedding_subtypeVal.isInducing.pseudoMetrizableSpace
  let := D.unipotentHaar_rightInvariant
  let := D₀.unipotentHaar_rightInvariant
  let := D₀.unipotentHaar_isHaar
  let _ : D₀.unipotentHaar.Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure D₀.unipotentHaar
  let := D.compatible.regular
  let := D₀.compatible.regular
  exact QuotientIntegration.exists_pos_smul_eq_of_rightInvariant_quotient H hH
    D₀.unipotentHaar D.measure D₀.measure D.compatible.nonzero D₀.compatible.nonzero
    D.compatible.right_invariant D₀.compatible.right_invariant

/-- The real unequal-rank package transfers to any compatible quotient measure.
Its self-dual rectangular measure is fixed. -/
theorem UnequalEquation.change_quotient_measure {r t : ℕ} {h : t < r} {a b : ℝˣ}
    {D₀ : RealQuotientMeasureData t}
    {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ} {W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ}
    {ds es dds ees : List RealBlock} {sign : ℂ}
    (hEq : UnequalEquation h a D₀ W W' ds es dds ees b sign) (D : RealQuotientMeasureData t) :
    UnequalEquation h a D W W' ds es dds ees b sign := by
  obtain ⟨c, _, hc⟩ := quotientMeasure_eq_pos_smul D D₀
  have hZ : realUnequalIntegral h D W W' =
      fun s => ((ENNReal.ofReal c).toReal : ℂ) * realUnequalIntegral h D₀ W W' s := by
    funext s
    simp only [realUnequalIntegral, ArchimedeanLocal.unequalIntegral, hc, integral_smul_measure,
      Complex.real_smul]
  have hZd : realUnequalDualIntegral h a D W W' =
      fun s => ((ENNReal.ofReal c).toReal : ℂ) * realUnequalDualIntegral h a D₀ W W' s := by
    funext s
    simp only [realUnequalDualIntegral, blockIntegral, hc, integral_smul_measure, Complex.real_smul]
  unfold UnequalEquation at hEq ⊢
  rw [hZ, hZd, realUnequalDualMeasure, hc, Measure.prod_smul_left]
  exact hEq.smul_measures c

/-- The real equal-rank package transfers to any compatible quotient measure,
with its Fourier and epsilon parameters fixed. -/
theorem EqualEquation.change_quotient_measure {r : ℕ} {a b : ℝˣ}
    {D₀ : RealQuotientMeasureData r} {W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    {Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ} {ds es dds ees : List RealBlock} {sign : ℂ}
    (hEq : EqualEquation a b D₀ W W' Φ ds es dds ees sign) (D : RealQuotientMeasureData r) :
    EqualEquation a b D W W' Φ ds es dds ees sign := by
  obtain ⟨c, _, hc⟩ := quotientMeasure_eq_pos_smul D D₀
  have hZ (V V' : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (f : (Fin (r + 1) → ℝ) → ℂ) :
      realEqualIntegral D V V' f =
        fun s => ((ENNReal.ofReal c).toReal : ℂ) * realEqualIntegral D₀ V V' f s := by
    funext s
    simp only [realEqualIntegral, equalIntegral, hc, integral_smul_measure, Complex.real_smul]
  unfold EqualEquation at hEq ⊢
  rw [show realEqualDualIntegral b D W W' Φ =
    realEqualIntegral D (ArchimedeanLocal.dualFunction (r + 1) W)
      (ArchimedeanLocal.dualFunction (r + 1) W')
      (realFourierTransform b Φ) from rfl, hZ, hZ, hc]
  exact hEq.smul_measures c

end RealJacquet

/-- Both real local equation packages are independent of the compatible quotient measure. -/
def RealJacquetQuotientMeasureIndependenceStatement : Prop := by
  classical
  exact
  (∀ (r t : ℕ) (h : t < r) (a b : ℝˣ) (D D₀ : RealQuotientMeasureData t)
    (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ)
    (ds es dds ees : List RealBlock) (sign : ℂ),
    RealJacquet.UnequalEquation h a D W W' ds es dds ees b sign ↔
      RealJacquet.UnequalEquation h a D₀ W W' ds es dds ees b sign) ∧
  (∀ (r : ℕ) (a b : ℝˣ) (D D₀ : RealQuotientMeasureData r)
    (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ) (ds es dds ees : List RealBlock) (sign : ℂ),
    RealJacquet.EqualEquation a b D W W' Φ ds es dds ees sign ↔
      RealJacquet.EqualEquation a b D₀ W W' Φ ds es dds ees sign)

theorem realJacquetQuotientMeasureIndependence : RealJacquetQuotientMeasureIndependenceStatement := by
  constructor
  · intro r t h a b D D₀ W W' ds es dds ees sign
    exact ⟨fun hEq => hEq.change_quotient_measure D₀, fun hEq => hEq.change_quotient_measure D⟩
  · intro r a b D D₀ W W' Φ ds es dds ees sign
    exact ⟨fun hEq => hEq.change_quotient_measure D₀, fun hEq => hEq.change_quotient_measure D⟩

end Langlands.Global.RankinSelbergGlobal
