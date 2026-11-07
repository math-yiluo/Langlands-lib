import Langlands.LocalFactor.Abelian.Padic
import Langlands.LocalField.Normalization.SpectralCharacter

/-! # Normalized character twists and the actual spectral abelian epsilon expression -/

noncomputable section

universe uF

namespace Langlands.PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology

/-- The actual normalized absolute-value power is trivial on all integral units. -/
theorem isUnramified_normalizedAbsPowerCharacter (s : ℂ) :
    T.IsUnramifiedQuasicharacter (T.normalizedAbsPowerCharacter s) := by
  intro a ha
  apply Units.ext
  rw [normalizedAbsPowerCharacter_apply, T.normalizedAbs_of_ne_zero a.ne_zero]
  simp [ord, ha]

/-- Multiplication by an actual unramified character preserves every unit
triviality level, including level zero. -/
theorem multiplicativeTrivialAt_unramified_mul_iff
    (ν χ : Character) (hν : T.IsUnramifiedQuasicharacter ν) (n : ℕ) :
    T.MultiplicativeTrivialAt (ν * χ) n ↔ T.MultiplicativeTrivialAt χ n := by
  constructor
  · intro h a ha
    simpa only [ContinuousMonoidHom.mul_apply, hν a ha.1, one_mul] using h a ha
  · intro h a ha
    simpa only [ContinuousMonoidHom.mul_apply, hν a ha.1, one_mul] using h a ha

/-- The least actual conductor is unchanged by an unramified character twist. -/
theorem multiplicativeConductor_unramified_mul
    (ν χ : Character) (hν : T.IsUnramifiedQuasicharacter ν) :
    T.multiplicativeConductor (ν * χ) = T.multiplicativeConductor χ := by
  apply le_antisymm
  · apply (T.multiplicativeTrivialAt_iff_conductor_le (ν * χ) _).1
    exact (T.multiplicativeTrivialAt_unramified_mul_iff ν χ hν _).2
      (T.multiplicativeConductor_spec χ)
  · apply (T.multiplicativeTrivialAt_iff_conductor_le χ _).1
    exact (T.multiplicativeTrivialAt_unramified_mul_iff ν χ hν _).1
      (T.multiplicativeConductor_spec (ν * χ))

@[simp]
theorem multiplicativeConductor_normalizedAbsPower_mul (s : ℂ) (χ : Character) :
    T.multiplicativeConductor (T.normalizedAbsPowerCharacter s * χ) =
      T.multiplicativeConductor χ :=
  T.multiplicativeConductor_unramified_mul _ χ
    (T.isUnramified_normalizedAbsPowerCharacter s)

end Langlands.PadicField.TopologicalData

namespace Langlands.LocalFactor.PadicAbelian

open MeasureTheory

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology (@borel F.Carrier T.topology)

/-- The normalized power has precisely the existing spectral variable as
its value on the specified uniformizer. -/
theorem normalizedAbsPowerCharacter_uniformizer (s : ℂ) :
    (T.normalizedAbsPowerCharacter s (uniformizerUnit T) : ℂ) = spectralVariable T s := by
  change (((LocalFactor.spectralParameter T.residueCardinality
      (by exact_mod_cast (zero_lt_one.trans T.residueCardinality_gt_one)) s) ^
      T.ord (uniformizerUnit T : F.Carrier) : ℂˣ) : ℂ) = _
  rw [uniformizerUnit_ord, zpow_one]
  rfl

/-- The inverse normalized power produces the same plus-sign spectral
Gauss integrand, including the zero value at the origin. -/
theorem epsilonIntegrand_normalizedAbsPower_mul
    (χ : Character) (ψ : AdditiveCharacter) (s : ℂ) (x : F.Carrier) :
    letI := T.topology
    HarmonicAnalysis.Quasicharacter.epsilonIntegrand
      (T.normalizedAbsPowerCharacter s * χ) ψ x =
        gaussIntegrand T χ ψ.toAddChar s x := by
  let := T.topology
  classical
  by_cases hx : x = 0
  · simp [HarmonicAnalysis.Quasicharacter.epsilonIntegrand,
      gaussIntegrand, characterExtension, hx]
  · simp only [HarmonicAnalysis.Quasicharacter.epsilonIntegrand,
      HarmonicAnalysis.Quasicharacter.extendZero, characterExtension,
      gaussIntegrand, dite_eq_right hx, ContinuousMonoidHom.mul_apply, Units.val_mul,
      PadicField.TopologicalData.normalizedAbsPowerCharacter_apply,
      HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply, mul_inv_rev,
      ← Complex.exp_neg, neg_mul, Units.val_mk0]

/-- Twisting the character and evaluating at zero gives the existing
spectral expression at the same parameter and the same actual Haar measure. -/
theorem epsilon_normalizedAbsPower_mul_zero
    (χ : Character) (ψ : AdditiveCharacter) (μ : LocalHaar) (s : ℂ) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    epsilon T (T.normalizedAbsPowerCharacter s * χ) ψ μ.measure 0 =
      epsilon T χ ψ μ.measure s := by
  let := T.topology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  classical
  simp only [epsilon, T.multiplicativeConductor_normalizedAbsPower_mul]
  unfold epsilonAt
  by_cases h : T.multiplicativeConductor χ = 0
  · simp only [h, ite_true, ContinuousMonoidHom.mul_apply, Units.val_mul,
      normalizedAbsPowerCharacter_uniformizer, mul_zpow, sub_zero, mul_one]
    rw [spectralVariable, ← Complex.exp_int_mul]
    have he :
        Complex.exp ((T.additiveConductor ψ : ℂ) *
          (-s * (Real.log (T.residueCardinality : ℝ) : ℂ))) *
        Complex.exp ((T.additiveConductor ψ : ℂ) *
          (Real.log (T.residueCardinality : ℝ) : ℂ)) =
        Complex.exp ((T.additiveConductor ψ : ℂ) * (1 - s) *
          (Real.log (T.residueCardinality : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [show ∀ a b c d : ℂ, (a * b * c) * d = b * (a * c) * d by
      intros; ring, he]
  · simp only [h, ite_false, gaussIntegrand_zero,
      epsilonIntegrand_normalizedAbsPower_mul]

/-- The normalized character twist of the actual abelian expression is
the full fixed-Haar spectral epsilon expression. -/
theorem abelianEpsilonExpression_normalizedAbsPower_mul
    (χ : Character) (ψ : AdditiveCharacter) (μ : LocalHaar) (s : ℂ) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    T.abelianEpsilonExpression (T.normalizedAbsPowerCharacter s * χ) ψ μ =
      epsilon T χ ψ μ.measure s := by
  rw [← deligneConstant_eq_abelianEpsilonExpression, deligneConstant]
  exact epsilon_normalizedAbsPower_mul_zero T χ ψ μ s

/-- The all-field, all-parameter comparison at every supplied actual Haar measure. -/
def NormalizedTwistEpsilonStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    ∀ (χ : HarmonicAnalysis.Quasicharacter F.Carrier)
      (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier)
      (μ : HarmonicAnalysis.AdditiveHaarMeasure F.Carrier) (s : ℂ),
      T.abelianEpsilonExpression (T.normalizedAbsPowerCharacter s * χ) ψ μ =
        epsilon T χ ψ μ.measure s

theorem normalizedTwistEpsilonProof : NormalizedTwistEpsilonStatement.{uF} := by
  intro p hp F T χ ψ μ s
  exact abelianEpsilonExpression_normalizedAbsPower_mul T χ ψ μ s

end Langlands.LocalFactor.PadicAbelian
