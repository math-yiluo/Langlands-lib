import Langlands.LocalFactor.Abelian.Padic
import Mathlib.Algebra.Polynomial.Laurent

/-!
# Laurent and rational models of the actual rank-one epsilon expression

The coefficient is the constructed Gauss constant and the integer exponent
retains both conductors. Evaluation is defined only at nonzero variables.
-/

noncomputable section

open MeasureTheory

namespace Langlands.LocalFactor.PadicAbelian

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "MultiplicativeCharacter" =>
  @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology
    (@borel F.Carrier T.topology)

/-- The full fixed-character spectral exponent, including additive conductor. -/
def epsilonExponent (χ : MultiplicativeCharacter) (ψ : AdditiveCharacter) : ℤ :=
  (T.multiplicativeConductor χ : ℤ) + T.additiveConductor ψ

/-- The actual spectral variable is nonzero at every finite complex argument. -/
theorem spectralVariable_ne_zero (s : ℂ) : spectralVariable T s ≠ 0 :=
  Complex.exp_ne_zero _

private theorem spectralVariable_zpow (s : ℂ) (d : ℤ) :
    spectralVariable T s ^ d =
      Complex.exp (-s * (Real.log ((T.residueCardinality : ℝ) ^ d) : ℂ)) := by
  rw [Real.log_zpow, Complex.ofReal_mul, Complex.ofReal_intCast]
  rw [spectralVariable, ← Complex.exp_int_mul]
  congr 1
  ring

/-- The monomial expression is derived from the actual convergent Gauss formula.
This is not an invocation of an epsilon functional equation. -/
theorem epsilon_eq_constant_mul_spectral_pow
    (χ : MultiplicativeCharacter) (ψ : AdditiveCharacter) (μ : LocalHaar) (s : ℂ) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    epsilon T χ ψ μ.measure s =
      deligneConstant T χ ψ μ.measure *
        spectralVariable T s ^ epsilonExponent T χ ψ := by
  let := T.topology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  classical
  by_cases h : T.multiplicativeConductor χ = 0
  · simp only [epsilon, epsilonAt, deligneConstant, h, ite_true, epsilonExponent,
      Nat.cast_zero, zero_add, sub_zero, mul_one]
    rw [spectralVariable, ← Complex.exp_int_mul]
    have he : Complex.exp ((T.additiveConductor ψ : ℂ) *
        (1 - s) * (Real.log (T.residueCardinality : ℝ) : ℂ)) =
        Complex.exp ((T.additiveConductor ψ : ℂ) *
          (Real.log (T.residueCardinality : ℝ) : ℂ)) *
        Complex.exp ((T.additiveConductor ψ : ℂ) *
          (-s * (Real.log (T.residueCardinality : ℝ) : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [he]
    ring
  · have hi :
        (∫ x in gaussShell T (T.additiveConductor ψ + T.multiplicativeConductor χ),
          gaussIntegrand T χ ψ.toAddChar s x ∂μ.measure) =
        Complex.exp (-s * (Real.log ((T.residueCardinality : ℝ) ^
          (T.additiveConductor ψ + T.multiplicativeConductor χ)) : ℂ)) *
        (∫ x in gaussShell T (T.additiveConductor ψ + T.multiplicativeConductor χ),
          HarmonicAnalysis.Quasicharacter.epsilonIntegrand χ ψ x ∂μ.measure) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun
      · rw [gaussShell_eq_valuationShell]
        exact (T.valuationShell_compact_closed _).2.measurableSet
      · intro x hx
        exact gaussIntegrand_on_shell T χ ψ _ s hx
    simp only [epsilon, epsilonAt, deligneConstant, h, ite_false,
      gaussIntegrand_zero]
    rw [hi, spectralVariable_zpow]
    simp only [epsilonExponent, add_comm (T.multiplicativeConductor χ : ℤ)]
    ring

/-- The Laurent polynomial built from the actual Gauss constant.
Nonvanishing of that constant remains a separate theorem. -/
def epsilonLaurent (χ : MultiplicativeCharacter) (ψ : AdditiveCharacter)
    (μ : LocalHaar) : LaurentPolynomial ℂ :=
  letI := T.topology
  letI : MeasurableSpace F.Carrier := borel F.Carrier
  LaurentPolynomial.C (deligneConstant T χ ψ μ.measure) *
    LaurentPolynomial.T (epsilonExponent T χ ψ)

/-- Evaluation at a nonzero variable uses the Laurent ring homomorphism. -/
def epsilonLaurentValue (χ : MultiplicativeCharacter) (ψ : AdditiveCharacter)
    (μ : LocalHaar) (t : ℂˣ) : ℂ :=
  LaurentPolynomial.eval₂ (RingHom.id ℂ) t (epsilonLaurent T χ ψ μ)

theorem epsilonLaurentValue_eq (χ : MultiplicativeCharacter) (ψ : AdditiveCharacter)
    (μ : LocalHaar) (t : ℂˣ) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    epsilonLaurentValue T χ ψ μ t =
      deligneConstant T χ ψ μ.measure * (t : ℂ) ^ epsilonExponent T χ ψ := by
  simp [epsilonLaurentValue, epsilonLaurent]

/-- The Laurent model evaluates to the existing spectral expression everywhere
in the complex spectral parameter, because `q^(-s)` is always nonzero. -/
theorem epsilonLaurentValue_spectral
    (χ : MultiplicativeCharacter) (ψ : AdditiveCharacter) (μ : LocalHaar) (s : ℂ) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    epsilonLaurentValue T χ ψ μ
      (Units.mk0 (spectralVariable T s) (spectralVariable_ne_zero T s)) =
        epsilon T χ ψ μ.measure s := by
  rw [epsilonLaurentValue_eq, epsilon_eq_constant_mul_spectral_pow]
  rfl

/-- The rational model is the image of the Laurent model under `T ↦ X`.
Negative exponents remain genuine rational functions. -/
def rationalEpsilon (χ : MultiplicativeCharacter) (ψ : AdditiveCharacter)
    (μ : LocalHaar) : RatFunc ℂ :=
  LaurentPolynomial.eval₂ RatFunc.C (Units.mk0 RatFunc.X RatFunc.X_ne_zero)
    (epsilonLaurent T χ ψ μ)

theorem rationalEpsilon_eq (χ : MultiplicativeCharacter) (ψ : AdditiveCharacter)
    (μ : LocalHaar) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    rationalEpsilon T χ ψ μ =
      RatFunc.C (deligneConstant T χ ψ μ.measure) *
        RatFunc.X ^ epsilonExponent T χ ψ := by
  simp [rationalEpsilon, epsilonLaurent]

/-- Nonvanishing of the rational object is precisely the still separate
nonvanishing of its constructed Gauss coefficient. -/
theorem rationalEpsilon_ne_zero_iff
    (χ : MultiplicativeCharacter) (ψ : AdditiveCharacter) (μ : LocalHaar) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    rationalEpsilon T χ ψ μ ≠ 0 ↔ deligneConstant T χ ψ μ.measure ≠ 0 := by
  let := T.topology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  rw [rationalEpsilon_eq, mul_ne_zero_iff]
  have hx : (RatFunc.X : RatFunc ℂ) ^ epsilonExponent T χ ψ ≠ 0 :=
    zpow_ne_zero _ RatFunc.X_ne_zero
  rw [and_iff_left hx]
  simpa only [map_zero] using
    (RatFunc.C_injective.ne_iff : RatFunc.C (deligneConstant T χ ψ μ.measure) ≠
      RatFunc.C 0 ↔ deligneConstant T χ ψ μ.measure ≠ 0)

end Langlands.LocalFactor.PadicAbelian
