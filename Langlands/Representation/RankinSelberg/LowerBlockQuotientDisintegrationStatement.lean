import Langlands.Group.GL.LowerBlockQuotientCoordinates
import Langlands.Group.GL.NormalizedCharacter
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Representation.RankinSelberg.QuotientIntegrals
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Lower-block disintegration of the left-unipotent quotient

The determinant density `[g] ↦ |det g|^(-d)` on `N_a \ GL_a`, defined by actual
quotient descent, and the proposition that every compatible quotient measure on
`N_(a+d) \ GL_(a+d)` is a positive multiple of the pushforward, under the published
lower-block chart `([g], x, h) ↦ [[[g,0],[x,h]]]`, of the weighted product
`D μ_a × dx × ρ` with `ρ` a right Haar measure on `B⁻_d` (JPSS §9.3, printed 456).
The proposition is stated, not proved.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis GeneralLinear QuotientIntegration
open scoped ENNReal

universe uF

section Density

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The representative weight `|det g|^(-d)` is invariant under left
multiplication by `N_m`, since upper-unipotent matrices have determinant one. -/
theorem lowerBlockDensity_unipotent_mul (T : F.TopologicalData) {m : ℕ} (d : ℕ)
    (u : upperUnipotent m F.Carrier) (g : Langlands.GeneralLinear m F.Carrier) :
    ENNReal.ofReal (T.normalizedAbs (Matrix.det (u.val * g).val)) ^ (-(d : ℤ)) =
      ENNReal.ofReal (T.normalizedAbs (Matrix.det g.val)) ^ (-(d : ℤ)) := by
  rw [Units.val_mul, Matrix.det_mul, unipotent_det, one_mul]

/-- The actual determinant density `[g] ↦ |det g|^(-d)` on `N_m \ GL_m`,
with the residue-normalized absolute value of `T`, defined by quotient descent. -/
def lowerBlockQuotientDensity (T : F.TopologicalData) (m d : ℕ) :
    LeftQuotient (upperUnipotent m F.Carrier) → ℝ≥0∞ :=
  descend _ (fun g => ENNReal.ofReal (T.normalizedAbs (Matrix.det g.val)) ^ (-(d : ℤ)))
    (lowerBlockDensity_unipotent_mul T d)

@[simp] theorem lowerBlockQuotientDensity_mk (T : F.TopologicalData) (m d : ℕ)
    (g : Langlands.GeneralLinear m F.Carrier) :
    lowerBlockQuotientDensity T m d (Quotient.mk _ g) =
      ENNReal.ofReal (T.normalizedAbs (Matrix.det g.val)) ^ (-(d : ℤ)) := rfl

/-- The density takes only finite values, because determinants of invertible
matrices have positive absolute value. -/
theorem lowerBlockQuotientDensity_ne_top (T : F.TopologicalData) (m d : ℕ)
    (q : LeftQuotient (upperUnipotent m F.Carrier)) :
    lowerBlockQuotientDensity T m d q ≠ ∞ := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [lowerBlockQuotientDensity_mk]
    have hpos : 0 < T.normalizedAbs (Matrix.det g.val) := by
      rcases (T.normalizedAbs_nonneg (Matrix.det g.val)).lt_or_eq with h | h
      · exact h
      · exact absurd ((T.normalizedAbs_eq_zero_iff _).mp h.symm)
          (Matrix.GeneralLinearGroup.det_ne_zero g)
    exact ENNReal.zpow_ne_top (ENNReal.ofReal_pos.mpr hpos).ne' ENNReal.ofReal_ne_top _

/-- The density is continuous for the quotient topology. -/
theorem continuous_lowerBlockQuotientDensity (T : F.TopologicalData) (m d : ℕ) :
    letI := T.topology
    Continuous (lowerBlockQuotientDensity T m d) := by
  let := T.topology
  have hdet : Continuous fun g : Langlands.GeneralLinear m F.Carrier =>
      ENNReal.ofReal (T.normalizedAbs (Matrix.det g.val)) :=
    ENNReal.continuous_ofReal.comp (NNReal.continuous_coe.comp
      (Units.continuous_val.comp (T.determinantNormContinuous m).continuous))
  have hf : Continuous fun g : Langlands.GeneralLinear m F.Carrier =>
      ENNReal.ofReal (T.normalizedAbs (Matrix.det g.val)) ^ (-(d : ℤ)) :=
    (ENNReal.continuous_zpow _).comp hdet
  exact hf.quotient_lift _

/-- The density is Borel measurable on the quotient. -/
theorem measurable_lowerBlockQuotientDensity (T : F.TopologicalData) (m d : ℕ) :
    letI := T.topology
    letI := borel (LeftQuotient (upperUnipotent m F.Carrier))
    Measurable (lowerBlockQuotientDensity T m d) := by
  let := T.topology
  let := borel (LeftQuotient (upperUnipotent m F.Carrier))
  have : BorelSpace (LeftQuotient (upperUnipotent m F.Carrier)) := ⟨rfl⟩
  exact (continuous_lowerBlockQuotientDensity T m d).measurable

end Density

/-- Lower-block disintegration of the actual left-unipotent quotient, in ranks
`a = n + 1`, `d = k + 1` and `a + d`. For compatible quotient measures `μa` and
`μad`, the published chart `([g], x, h) ↦ [[[g,0],[x,h]]]` is an open measurable
embedding with `μad`-conull range, and there are a right Haar measure `ρ` on the
lower-triangular group and a constant `C > 0` with
`μad = C • map chart ((μa.withDensity D).prod (dx.prod ρ))`,
`D [g] = |det g|^(-d)`, together with the resulting integrability and integral
transfer for Borel measurable complex functions. -/
def LowerBlockQuotientDisintegrationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (n k : ℕ),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftQuotient (upperUnipotent (n + 1) F.Carrier))
    letI : BorelSpace (LeftQuotient (upperUnipotent (n + 1) F.Carrier)) := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1 + k + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1 + k + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1 + k + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1 + k + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftQuotient (upperUnipotent (n + 1 + k + 1) F.Carrier))
    letI : BorelSpace (LeftQuotient (upperUnipotent (n + 1 + k + 1) F.Carrier)) := ⟨rfl⟩
    letI := borel (lowerTriangularSubgroup (k + 1) F.Carrier)
    letI : BorelSpace (lowerTriangularSubgroup (k + 1) F.Carrier) := ⟨rfl⟩
    let chart : LowerBlockQuotientParameters (n + 1) (k + 1) F.Carrier →
        LeftQuotient (upperUnipotent (n + 1 + k + 1) F.Carrier) :=
      lowerBlockQuotientChart
    let D : LeftQuotient (upperUnipotent (n + 1) F.Carrier) → ℝ≥0∞ :=
      lowerBlockQuotientDensity F.canonicalTopologicalData (n + 1) (k + 1)
    ∀ (η : AdditiveHaarMeasure F.Carrier),
    let dx : Measure (Matrix (Fin (k + 1)) (Fin (n + 1)) F.Carrier) :=
      rectangularMeasure η (k + 1) (n + 1)
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (n + 1 + k))],
    ∀ (μa : Measure (LeftQuotient (upperUnipotent (n + 1) F.Carrier)))
      (μad : Measure (LeftQuotient (upperUnipotent (n + 1 + k + 1) F.Carrier))),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μa →
      IsCompatible (upperUnipotent (n + 1 + k + 1) F.Carrier)
        (generalLinearHaar F.Carrier (n + 1 + k)) (unipotentHaar F.Carrier (n + 1 + k)) μad →
      Topology.IsOpenEmbedding chart ∧ Measurable chart ∧ μad (Set.range chart)ᶜ = 0 ∧
      (∀ K : OpenAddSubgroup (Matrix (Fin (k + 1)) (Fin (n + 1)) F.Carrier),
        IsCompact (K : Set (Matrix (Fin (k + 1)) (Fin (n + 1)) F.Carrier)) →
          0 < dx K ∧ dx K < ∞) ∧
      ∃ ρ : Measure (lowerTriangularSubgroup (k + 1) F.Carrier),
        ρ.Regular ∧ SigmaFinite ρ ∧ ρ.IsOpenPosMeasure ∧ IsFiniteMeasureOnCompacts ρ ∧
        ρ.IsMulRightInvariant ∧
        (∀ K : OpenSubgroup (lowerTriangularSubgroup (k + 1) F.Carrier),
          IsCompact (K : Set (lowerTriangularSubgroup (k + 1) F.Carrier)) →
            0 < ρ K ∧ ρ K < ∞) ∧
        ∃ C : ℝ, 0 < C ∧
          μad = ENNReal.ofReal C • Measure.map chart ((μa.withDensity D).prod (dx.prod ρ)) ∧
          ∀ f : LeftQuotient (upperUnipotent (n + 1 + k + 1) F.Carrier) → ℂ, Measurable f →
            (Integrable f μad ↔
              Integrable (f ∘ chart) ((μa.withDensity D).prod (dx.prod ρ))) ∧
            (Integrable f μad →
              ∫ q, f q ∂μad =
                (C : ℂ) * ∫ z, f (chart z) ∂(μa.withDensity D).prod (dx.prod ρ))

end Langlands.RankinSelberg
