import Langlands.LocalFactor.Abelian.Laurent
import Langlands.LocalFactor.Abelian.SpectralTransport

/-!
# Direct abelian gamma on the common regular domain

The construction uses the actual Gauss epsilon expression and the reflected
inverse-character L-ratio. Nonvanishing of the Gauss coefficient is not assumed.
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

/-- Both individual L-values are evaluated only at their regular points.
This need not be the maximal domain of the ratio after cancellation. -/
def GammaRegularAt (χ : MultiplicativeCharacter) (s : ℂ) : Prop :=
  RegularPoint T (uniformizerUnit T) χ (T.multiplicativeConductor χ) s ∧
    RegularPoint T (uniformizerUnit T) χ⁻¹ (T.multiplicativeConductor χ⁻¹) (1 - s)

/-- The common regular domain, retaining the original complex coordinate. -/
abbrev GammaRegularPoint (χ : MultiplicativeCharacter) :=
  {s : ℂ // GammaRegularAt T χ s}

theorem gammaRegularAt_iff_polynomial_ne_zero (χ : MultiplicativeCharacter) (s : ℂ) :
    GammaRegularAt T χ s ↔
      (lPolynomial T χ).eval (spectralVariable T s) ≠ 0 ∧
      (lPolynomial T χ⁻¹).eval (spectralVariable T (1 - s)) ≠ 0 := by
  simp only [GammaRegularAt, regularPoint_iff_polynomial_ne_zero]

/-- The unit-valued ratio `L(1-s,χ⁻¹) / L(s,χ)` on its common regular domain. -/
def gammaLRatio (χ : MultiplicativeCharacter) (s : GammaRegularPoint T χ) : ℂˣ :=
  regularLValue T χ⁻¹ ⟨1 - s.val, s.property.2⟩ /
    regularLValue T χ ⟨s.val, s.property.1⟩

theorem coe_gammaLRatio (χ : MultiplicativeCharacter) (s : GammaRegularPoint T χ) :
    (gammaLRatio T χ s : ℂ) = lFactor T χ⁻¹ (1 - s.val) / lFactor T χ s.val := by
  simp only [gammaLRatio, Units.val_div_eq_div_val, coe_regularLValue]

/-- The numerator is the original Euler polynomial; the denominator is the
inverse-character polynomial at the reflected coordinate. -/
theorem gammaLRatio_eq_polynomial_ratio
    (χ : MultiplicativeCharacter) (s : GammaRegularPoint T χ) :
    (gammaLRatio T χ s : ℂ) =
      (lPolynomial T χ).eval (spectralVariable T s.val) /
        (lPolynomial T χ⁻¹).eval (spectralVariable T (1 - s.val)) := by
  simp only [gammaLRatio, Units.val_div_eq_div_val, regularLValue,
    Units.val_inv_eq_inv_val, Units.val_mk0]
  exact inv_div_inv _ _

/-- The direct fixed-Haar abelian gamma expression from the actual epsilon.
It is complex-valued until the Gauss coefficient's nonvanishing is proved. -/
def gammaValue (χ : MultiplicativeCharacter) (ψ : AdditiveCharacter)
    (μ : LocalHaar) (s : GammaRegularPoint T χ) : ℂ :=
  letI := T.topology
  letI : MeasurableSpace F.Carrier := borel F.Carrier
  epsilon T χ ψ μ.measure s.val * (gammaLRatio T χ s : ℂ)

theorem gammaValue_formula (χ : MultiplicativeCharacter) (ψ : AdditiveCharacter)
    (μ : LocalHaar) (s : GammaRegularPoint T χ) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    gammaValue T χ ψ μ s =
      epsilon T χ ψ μ.measure s.val *
        (lFactor T χ⁻¹ (1 - s.val) / lFactor T χ s.val) := by
  rw [gammaValue, coe_gammaLRatio]

/-- The coefficient and exponent come from the actual convergent Gauss formula. -/
theorem gammaValue_eq_constant_mul_spectral_pow
    (χ : MultiplicativeCharacter) (ψ : AdditiveCharacter)
    (μ : LocalHaar) (s : GammaRegularPoint T χ) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    gammaValue T χ ψ μ s =
      deligneConstant T χ ψ μ.measure *
        spectralVariable T s.val ^ epsilonExponent T χ ψ *
        ((lPolynomial T χ).eval (spectralVariable T s.val) /
          (lPolynomial T χ⁻¹).eval (spectralVariable T (1 - s.val))) := by
  rw [gammaValue, epsilon_eq_constant_mul_spectral_pow, gammaLRatio_eq_polynomial_ratio]

/-- On this domain, gamma vanishes exactly when the actual epsilon does. -/
theorem gammaValue_ne_zero_iff_epsilon
    (χ : MultiplicativeCharacter) (ψ : AdditiveCharacter)
    (μ : LocalHaar) (s : GammaRegularPoint T χ) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    gammaValue T χ ψ μ s ≠ 0 ↔ epsilon T χ ψ μ.measure s.val ≠ 0 := by
  rw [gammaValue, mul_ne_zero_iff, and_iff_left (Units.ne_zero _)]

/-- Nonvanishing reduces to the still separate Gauss-coefficient theorem. -/
theorem gammaValue_ne_zero_iff_constant
    (χ : MultiplicativeCharacter) (ψ : AdditiveCharacter)
    (μ : LocalHaar) (s : GammaRegularPoint T χ) :
    letI := T.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    gammaValue T χ ψ μ s ≠ 0 ↔ deligneConstant T χ ψ μ.measure ≠ 0 := by
  rw [gammaValue_ne_zero_iff_epsilon, epsilon_eq_constant_mul_spectral_pow,
    mul_ne_zero_iff, and_iff_left (zpow_ne_zero _ (spectralVariable_ne_zero T s.val))]

end Langlands.LocalFactor.PadicAbelian

namespace Langlands.PadicField.AbelianTransport

open HarmonicAnalysis ConductorTransport LocalFactor.PadicAbelian

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  (e : F.Carrier ≃ₐ[Padic p] E.Carrier)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : TopologicalSpace E.Carrier := E.canonicalTopologicalData.topology
local instance : MeasurableSpace F.Carrier := borel F.Carrier
local instance : MeasurableSpace E.Carrier := borel E.Carrier

/-- Inverse pullback commutes with pointwise inversion of quasicharacters. -/
@[simp] theorem quasicharacter_inv (χ : Quasicharacter F.Carrier) :
    quasicharacter F E e χ⁻¹ = (quasicharacter F E e χ)⁻¹ := by
  ext x
  rfl

/-- Both halves of the common regularity predicate survive field transport. -/
theorem gammaRegularAt_iff (χ : Quasicharacter F.Carrier) (s : ℂ) :
    GammaRegularAt E.canonicalTopologicalData (quasicharacter F E e χ) s ↔
      GammaRegularAt F.canonicalTopologicalData χ s := by
  unfold GammaRegularAt
  rw [← quasicharacter_inv, regularPoint_iff, regularPoint_iff]

/-- Identity on the complex coordinate, with both regularity proofs transported. -/
def gammaRegularPointEquiv (χ : Quasicharacter F.Carrier) :
    GammaRegularPoint F.canonicalTopologicalData χ ≃
      GammaRegularPoint E.canonicalTopologicalData (quasicharacter F E e χ) where
  toFun s := ⟨s.val, (gammaRegularAt_iff F E e χ s.val).2 s.property⟩
  invFun s := ⟨s.val, (gammaRegularAt_iff F E e χ s.val).1 s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem gammaRegularPointEquiv_val (χ : Quasicharacter F.Carrier)
    (s : GammaRegularPoint F.canonicalTopologicalData χ) :
    (gammaRegularPointEquiv F E e χ s).val = s.val := rfl

/-- The reflected inverse-character ratio agrees at corresponding regular points. -/
theorem gammaLRatio_eq (χ : Quasicharacter F.Carrier)
    (s : GammaRegularPoint F.canonicalTopologicalData χ) :
    gammaLRatio E.canonicalTopologicalData (quasicharacter F E e χ)
      (gammaRegularPointEquiv F E e χ s) =
        gammaLRatio F.canonicalTopologicalData χ s := by
  apply Units.ext
  rw [gammaLRatio_eq_polynomial_ratio, gammaLRatio_eq_polynomial_ratio]
  simp only [gammaRegularPointEquiv_val, ← quasicharacter_inv,
    lPolynomial_eq, spectralVariable_eq F E e]

/-- The direct abelian gamma construction respects actual field transport,
with inverse-pullback characters and the pushforward Haar measure. -/
theorem gammaValue_eq (χ : Quasicharacter F.Carrier)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (s : GammaRegularPoint F.canonicalTopologicalData χ) :
    gammaValue E.canonicalTopologicalData (quasicharacter F E e χ)
      (additiveCharacter F E e ψ) (haarMeasure F E e μ)
      (gammaRegularPointEquiv F E e χ s) =
        gammaValue F.canonicalTopologicalData χ ψ μ s := by
  simp only [gammaValue, gammaRegularPointEquiv_val, epsilon_eq, gammaLRatio_eq]

end Langlands.PadicField.AbelianTransport
