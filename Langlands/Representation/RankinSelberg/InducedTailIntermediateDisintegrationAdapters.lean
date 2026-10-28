import Langlands.Representation.RankinSelberg.InducedTailIntermediateQuotientData
import Langlands.Representation.RankinSelberg.LowerBlockQuotientDisintegrationStatement
import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Group.GL.RankReindex

/-! # Rank and density adapters for actual lower-block disintegration -/

noncomputable section

namespace Langlands.RankinSelberg.InducedTailIntermediate

open GeneralLinear QuotientIntegration MeasureTheory HarmonicAnalysis
open scoped ENNReal

universe uF

section Rank

variable {F : Type uF} [Field F] [TopologicalSpace F]

/-- The published quotient rank homeomorphism is equality transport when its
rank equivalence comes from a numerical equality. -/
theorem upperUnipotentQuotientCongr_eq_cast {m n : ℕ} (h : m = n)
    (q : LeftQuotient (upperUnipotent m F)) :
    upperUnipotentQuotientCongr h q =
      cast (congrArg (fun r => LeftQuotient (upperUnipotent r F)) h) q := by
  subst n
  induction q using Quotient.inductionOn with
  | h g =>
    simp only [upperUnipotentQuotientCongr_mk, reindex_finCongr_rfl,
      MulEquiv.refl_apply]
    rfl

/-- Equality transport of an actual quotient measure. The Borel structures
on both numerically equal quotient ranks are fixed explicitly. -/
def quotientMeasureRankCast {m n : ℕ} (h : m = n)
    (μ : @Measure (LeftQuotient (upperUnipotent m F))
      (borel (LeftQuotient (upperUnipotent m F)))) :
    @Measure (LeftQuotient (upperUnipotent n F))
      (borel (LeftQuotient (upperUnipotent n F))) := h ▸ μ

/-- Mapping by the actual rank homeomorphism agrees with equality transport
of the measure; this is not an identification of measures in different ranks. -/
theorem map_upperUnipotentQuotientCongr {m n : ℕ} (h : m = n)
    (μ : @Measure (LeftQuotient (upperUnipotent m F))
      (borel (LeftQuotient (upperUnipotent m F)))) :
    letI := borel (LeftQuotient (upperUnipotent m F))
    letI := borel (LeftQuotient (upperUnipotent n F))
    Measure.map (upperUnipotentQuotientCongr h) μ = quotientMeasureRankCast h μ := by
  subst n
  have he : (upperUnipotentQuotientCongr (R := F) (rfl : m = m) :
      LeftQuotient (upperUnipotent m F) → LeftQuotient (upperUnipotent m F)) = id :=
    funext (upperUnipotentQuotientCongr_eq_cast rfl)
  simp only [he, Measure.map_id, quotientMeasureRankCast]

/-- Borel measurability is preserved and reflected by the actual rank
homeomorphism for a numerical equality. -/
theorem measurable_comp_upperUnipotentQuotientCongr {m n : ℕ} (h : m = n)
    (f : LeftQuotient (upperUnipotent n F) → ℂ) :
    letI := borel (LeftQuotient (upperUnipotent m F))
    letI := borel (LeftQuotient (upperUnipotent n F))
    Measurable (f ∘ upperUnipotentQuotientCongr h) ↔ Measurable f := by
  subst n
  have he : (upperUnipotentQuotientCongr (R := F) (rfl : m = m) :
      LeftQuotient (upperUnipotent m F) → LeftQuotient (upperUnipotent m F)) = id :=
    funext (upperUnipotentQuotientCongr_eq_cast rfl)
  simp only [he, Function.comp_id]

/-- Equality transport preserves actual absolute integrability, with no
normalization scalar. -/
theorem integrable_quotientMeasureRankCast_iff {m n : ℕ} (h : m = n)
    (μ : @Measure (LeftQuotient (upperUnipotent m F))
      (borel (LeftQuotient (upperUnipotent m F))))
    (f : LeftQuotient (upperUnipotent n F) → ℂ) :
    letI := borel (LeftQuotient (upperUnipotent m F))
    letI := borel (LeftQuotient (upperUnipotent n F))
    Integrable f (quotientMeasureRankCast h μ) ↔
      Integrable (f ∘ upperUnipotentQuotientCongr h) μ := by
  subst n
  have he : (upperUnipotentQuotientCongr (R := F) (rfl : m = m) :
      LeftQuotient (upperUnipotent m F) → LeftQuotient (upperUnipotent m F)) = id :=
    funext (upperUnipotentQuotientCongr_eq_cast rfl)
  simp only [quotientMeasureRankCast, he, Function.comp_id]

/-- The complex Bochner integral is unchanged by the same actual rank and
measure transport, including for functions without an integrability premise. -/
theorem integral_quotientMeasureRankCast {m n : ℕ} (h : m = n)
    (μ : @Measure (LeftQuotient (upperUnipotent m F))
      (borel (LeftQuotient (upperUnipotent m F))))
    (f : LeftQuotient (upperUnipotent n F) → ℂ) :
    letI := borel (LeftQuotient (upperUnipotent m F))
    letI := borel (LeftQuotient (upperUnipotent n F))
    ∫ q, f q ∂quotientMeasureRankCast h μ =
      ∫ q, f (upperUnipotentQuotientCongr h q) ∂μ := by
  subst n
  have he : (upperUnipotentQuotientCongr (R := F) (rfl : m = m) :
      LeftQuotient (upperUnipotent m F) → LeftQuotient (upperUnipotent m F)) = id :=
    funext (upperUnipotentQuotientCongr_eq_cast rfl)
  simp only [quotientMeasureRankCast, he, id_eq]

/-- The chart used by the span calculation is the published chart followed
only by equality transport of its actual matrix rank. -/
theorem quotientChart_eq_cast (n d : ℕ)
    (z : LeftUnipotentQuotient n F ×
      (Matrix (Fin d) (Fin (n + 1)) F × lowerTriangularSubgroup d F)) :
    quotientChart n d z =
      cast (congrArg (fun r => LeftQuotient (upperUnipotent r F))
        (by omega : (n + 1) + d = (n + d) + 1)) (lowerBlockQuotientChart z) :=
  upperUnipotentQuotientCongr_eq_cast _ _

end Rank

section Compatibility

variable {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F]
  [IsNonarchimedeanLocalField F]

/-- Numerical equality of JPSS indices preserves compatibility with the
actual normalized group and unipotent Haar measures. -/
theorem compatible_quotientMeasureRankCast_iff {m n : ℕ} (h : m = n) :
    letI := borel (Langlands.GeneralLinear (m + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (m + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (m + 1) F)
    letI : BorelSpace (upperUnipotent (m + 1) F) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient m F)
    letI : BorelSpace (LeftUnipotentQuotient m F) := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F)
    letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F)
    letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F m)]
      [Measure.IsMulRightInvariant (unipotentHaar F n)]
      (μ : Measure (LeftUnipotentQuotient m F)),
      IsCompatible (upperUnipotent (n + 1) F) (generalLinearHaar F n)
        (unipotentHaar F n) (quotientMeasureRankCast (congrArg (· + 1) h) μ) ↔
      IsCompatible (upperUnipotent (m + 1) F) (generalLinearHaar F m)
        (unipotentHaar F m) μ := by
  subst n
  intro _ _ μ
  rfl

end Compatibility

section Density

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The density in the span calculation equals the descended density in the
actual measure-disintegration statement, including its exponent and normalization. -/
theorem quotientDensity_eq_lowerBlockQuotientDensity (T : F.TopologicalData)
    (n d : ℕ) :
    quotientDensity (normalizedAbsoluteValue T) n d =
      lowerBlockQuotientDensity T (n + 1) d := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    rw [quotientDensity_eq_ofReal_zpow]
    rfl

end Density

end Langlands.RankinSelberg.InducedTailIntermediate
