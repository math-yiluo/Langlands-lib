import Langlands.Representation.RankinSelberg.LowerBlockQuotientDisintegrationStatement
import Langlands.AllField.Group.GL.NormalizedCharacterSupplement
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

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding LowerBlockQuotientDisintegrationStatement continuous_lowerBlockQuotientDensity lowerBlockDensity_unipotent_mul lowerBlockQuotientDensity lowerBlockQuotientDensity_mk measurable_lowerBlockQuotientDensity
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open scoped ENNReal

universe uF

section Density

variable {F : Type uF} [Field F]

/-- The representative weight `|det g|^(-d)` is invariant under left
multiplication by `N_m`, since upper-unipotent matrices have determinant one. -/
theorem lowerBlockDensity_unipotent_mul (T : LocalFieldData F) {m : ℕ} (d : ℕ)
    (u : upperUnipotent m F) (g : Langlands.GeneralLinear m F) :
    ENNReal.ofReal (T.normalizedAbs (Matrix.det (u.val * g).val)) ^ (-(d : ℤ)) =
      ENNReal.ofReal (T.normalizedAbs (Matrix.det g.val)) ^ (-(d : ℤ)) := by
  rw [Units.val_mul, Matrix.det_mul, unipotent_det, one_mul]

/-- The actual determinant density `[g] ↦ |det g|^(-d)` on `N_m \ GL_m`,
with the residue-normalized absolute value of `T`, defined by quotient descent. -/
def lowerBlockQuotientDensity (T : LocalFieldData F) (m d : ℕ) :
    LeftQuotient (upperUnipotent m F) → ℝ≥0∞ :=
  descend _ (fun g => ENNReal.ofReal (T.normalizedAbs (Matrix.det g.val)) ^ (-(d : ℤ)))
    (lowerBlockDensity_unipotent_mul T d)

@[simp] theorem lowerBlockQuotientDensity_mk (T : LocalFieldData F) (m d : ℕ)
    (g : Langlands.GeneralLinear m F) :
    lowerBlockQuotientDensity T m d (Quotient.mk _ g) =
      ENNReal.ofReal (T.normalizedAbs (Matrix.det g.val)) ^ (-(d : ℤ)) := rfl

/-- The density is continuous for the quotient topology. -/
theorem continuous_lowerBlockQuotientDensity (T : LocalFieldData F) (m d : ℕ) :
    letI := T.topology
    Continuous (lowerBlockQuotientDensity T m d) := by
  let := T.topology
  have hdet : Continuous fun g : Langlands.GeneralLinear m F =>
      ENNReal.ofReal (T.normalizedAbs (Matrix.det g.val)) :=
    ENNReal.continuous_ofReal.comp (NNReal.continuous_coe.comp
      (Units.continuous_val.comp (T.determinantNormContinuous m).continuous))
  have hf : Continuous fun g : Langlands.GeneralLinear m F =>
      ENNReal.ofReal (T.normalizedAbs (Matrix.det g.val)) ^ (-(d : ℤ)) :=
    (ENNReal.continuous_zpow _).comp hdet
  exact hf.quotient_lift _

/-- The density is Borel measurable on the quotient. -/
theorem measurable_lowerBlockQuotientDensity (T : LocalFieldData F) (m d : ℕ) :
    letI := T.topology
    letI := borel (LeftQuotient (upperUnipotent m F))
    Measurable (lowerBlockQuotientDensity T m d) := by
  let := T.topology
  let := borel (LeftQuotient (upperUnipotent m F))
  have : BorelSpace (LeftQuotient (upperUnipotent m F)) := ⟨rfl⟩
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
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (n k : ℕ),
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F)
    letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
    letI := borel (LeftQuotient (upperUnipotent (n + 1) F))
    letI : BorelSpace (LeftQuotient (upperUnipotent (n + 1) F)) := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1 + k + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1 + k + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1 + k + 1) F)
    letI : BorelSpace (upperUnipotent (n + 1 + k + 1) F) := ⟨rfl⟩
    letI := borel (LeftQuotient (upperUnipotent (n + 1 + k + 1) F))
    letI : BorelSpace (LeftQuotient (upperUnipotent (n + 1 + k + 1) F)) := ⟨rfl⟩
    letI := borel (lowerTriangularSubgroup (k + 1) F)
    letI : BorelSpace (lowerTriangularSubgroup (k + 1) F) := ⟨rfl⟩
    let chart : LowerBlockQuotientParameters (n + 1) (k + 1) F →
        LeftQuotient (upperUnipotent (n + 1 + k + 1) F) :=
      lowerBlockQuotientChart
    let D : LeftQuotient (upperUnipotent (n + 1) F) → ℝ≥0∞ :=
      lowerBlockQuotientDensity (⟨⟩ : LocalFieldData F) (n + 1) (k + 1)
    ∀ (η : AdditiveHaarMeasure F),
    let dx : Measure (Matrix (Fin (k + 1)) (Fin (n + 1)) F) :=
      rectangularMeasure η (k + 1) (n + 1)
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F n)],
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F (n + 1 + k))],
    ∀ (μa : Measure (LeftQuotient (upperUnipotent (n + 1) F)))
      (μad : Measure (LeftQuotient (upperUnipotent (n + 1 + k + 1) F))),
      IsCompatible (upperUnipotent (n + 1) F)
        (generalLinearHaar F n) (unipotentHaar F n) μa →
      IsCompatible (upperUnipotent (n + 1 + k + 1) F)
        (generalLinearHaar F (n + 1 + k)) (unipotentHaar F (n + 1 + k)) μad →
      Topology.IsOpenEmbedding chart ∧ Measurable chart ∧ μad (Set.range chart)ᶜ = 0 ∧
      (∀ K : OpenAddSubgroup (Matrix (Fin (k + 1)) (Fin (n + 1)) F),
        IsCompact (K : Set (Matrix (Fin (k + 1)) (Fin (n + 1)) F)) →
          0 < dx K ∧ dx K < ∞) ∧
      ∃ ρ : Measure (lowerTriangularSubgroup (k + 1) F),
        ρ.Regular ∧ SigmaFinite ρ ∧ ρ.IsOpenPosMeasure ∧ IsFiniteMeasureOnCompacts ρ ∧
        ρ.IsMulRightInvariant ∧
        (∀ K : OpenSubgroup (lowerTriangularSubgroup (k + 1) F),
          IsCompact (K : Set (lowerTriangularSubgroup (k + 1) F)) →
            0 < ρ K ∧ ρ K < ∞) ∧
        ∃ C : ℝ, 0 < C ∧
          μad = ENNReal.ofReal C • Measure.map chart ((μa.withDensity D).prod (dx.prod ρ)) ∧
          ∀ f : LeftQuotient (upperUnipotent (n + 1 + k + 1) F) → ℂ, Measurable f →
            (Integrable f μad ↔
              Integrable (f ∘ chart) ((μa.withDensity D).prod (dx.prod ρ))) ∧
            (Integrable f μad →
              ∫ q, f q ∂μad =
                (C : ℂ) * ∫ z, f (chart z) ∂(μa.withDensity D).prod (dx.prod ρ))

end Langlands.AllField.RankinSelberg
