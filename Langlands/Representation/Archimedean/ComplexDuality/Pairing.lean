import Langlands.Representation.Archimedean.ComplexDuality.GramWeight
import Langlands.Representation.Archimedean.ComplexLanglandsQuotientReduction

/-!
# The integration pairing on `U(n)`

The bilinear pairing `⟨f, h⟩ = ∫_{U(n)} f(k) h(k) dk` of the `U(n)`-finite functions of two
principal series of `GL_n(ℂ)`, for the Haar probability measure on `U(n)`. It is invariant under
right translation by `U(n)` and, for pointwise inverse characters, nondegenerate in the second
argument. `complexStandardDuality_of_lieInvariance` derives `ComplexStandardDualityStatement`
from the remaining `𝔤`-invariance of the integral.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator
open MeasureTheory

namespace Langlands.Archimedean.ComplexDuality

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

/-- `U(n)`-finite functions of a principal series are continuous. -/
theorem continuous_of_mem_kFiniteFunctions {χ : ℕ → ℂˣ → ℂ}
    {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)) :
    Continuous f :=
  (Submodule.mem_inf.mp hf).1.1.continuous

/-- The product of two continuous functions on `GL_n(ℂ)` is integrable on `U(n)`. -/
theorem integrable_mul_of_continuous {f h : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : Continuous f) (hh : Continuous h) :
    Integrable (fun k : unitaryCompact ℂ n =>
      f (k : Langlands.GeneralLinear n ℂ) * h (k : Langlands.GeneralLinear n ℂ)) (unitaryHaar n) :=
  integrable_unitaryHaar ((hf.comp continuous_subtype_val).mul (hh.comp continuous_subtype_val))

/-- The integration pairing `⟨f, h⟩ = ∫_{U(n)} f(k) h(k) dk` of the `U(n)`-finite functions of the
principal series of `χ` and of `χ'`. -/
def integralPairing (n : ℕ) (χ χ' : ℕ → ℂˣ → ℂ) :
    kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) →ₗ[ℂ]
      kFiniteFunctions (principalSeries ℂ n χ') (unitaryCompact ℂ n) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ
    (fun f h => ∫ k : unitaryCompact ℂ n,
      (f : Langlands.GeneralLinear n ℂ → ℂ) k * (h : Langlands.GeneralLinear n ℂ → ℂ) k
        ∂unitaryHaar n)
    (fun f₁ f₂ h => by
      rw [← integral_add (integrable_mul_of_continuous
          (continuous_of_mem_kFiniteFunctions f₁.2) (continuous_of_mem_kFiniteFunctions h.2))
        (integrable_mul_of_continuous
          (continuous_of_mem_kFiniteFunctions f₂.2) (continuous_of_mem_kFiniteFunctions h.2))]
      congr 1
      funext k
      simp only [Submodule.coe_add, Pi.add_apply, add_mul])
    (fun c f h => by
      rw [smul_eq_mul, ← integral_const_mul]
      congr 1
      funext k
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc])
    (fun f h₁ h₂ => by
      rw [← integral_add (integrable_mul_of_continuous
          (continuous_of_mem_kFiniteFunctions f.2) (continuous_of_mem_kFiniteFunctions h₁.2))
        (integrable_mul_of_continuous
          (continuous_of_mem_kFiniteFunctions f.2) (continuous_of_mem_kFiniteFunctions h₂.2))]
      congr 1
      funext k
      simp only [Submodule.coe_add, Pi.add_apply, mul_add])
    (fun c f h => by
      rw [smul_eq_mul, ← integral_const_mul]
      congr 1
      funext k
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      ring)

theorem integralPairing_apply (χ χ' : ℕ → ℂˣ → ℂ)
    (f : kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n))
    (h : kFiniteFunctions (principalSeries ℂ n χ') (unitaryCompact ℂ n)) :
    integralPairing n χ χ' f h =
      ∫ k : unitaryCompact ℂ n,
        (f : Langlands.GeneralLinear n ℂ → ℂ) k * (h : Langlands.GeneralLinear n ℂ → ℂ) k
          ∂unitaryHaar n :=
  rfl

/-- The integration pairing is invariant under right translation by `U(n)`: this is the right
invariance of the Haar measure of the compact group `U(n)`. -/
theorem integralPairing_rightTranslation (χ χ' : ℕ → ℂˣ → ℂ) (k : unitaryCompact ℂ n)
    (f : kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n))
    (h : kFiniteFunctions (principalSeries ℂ n χ') (unitaryCompact ℂ n))
    (hf : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
        (k : Langlands.GeneralLinear n ℂ) (f : Langlands.GeneralLinear n ℂ → ℂ) ∈
      kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n))
    (hh : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ)
        (k : Langlands.GeneralLinear n ℂ) (h : Langlands.GeneralLinear n ℂ → ℂ) ∈
      kFiniteFunctions (principalSeries ℂ n χ') (unitaryCompact ℂ n)) :
    integralPairing n χ χ' ⟨_, hf⟩ ⟨_, hh⟩ = integralPairing n χ χ' f h := by
  rw [integralPairing_apply, integralPairing_apply]
  exact integral_mul_right_eq_self (μ := unitaryHaar n)
    (fun x : unitaryCompact ℂ n => (f : Langlands.GeneralLinear n ℂ → ℂ) x *
      (h : Langlands.GeneralLinear n ℂ → ℂ) x) k

/-- The `𝔤`-invariance of the integral over `U(n)`: for pointwise inverse characters,
`∫_{U(n)} (R(X) f) h + ∫_{U(n)} f (R(X) h) = 0` on the principal series. -/
def IntegralLieInvariance : Prop :=
  ∀ (n : ℕ) (χ χ' : ℕ → ℂˣ → ℂ), (∀ i z, χ i z * χ' i z = 1) →
    ∀ (f h : Langlands.GeneralLinear n ℂ → ℂ), f ∈ principalSeries ℂ n χ →
      h ∈ principalSeries ℂ n χ' → ∀ X : Matrix (Fin n) (Fin n) ℂ,
        (∫ k : unitaryCompact ℂ n,
            rightDerivative (matrixModel ℂ n) X f (k : Langlands.GeneralLinear n ℂ) *
              h (k : Langlands.GeneralLinear n ℂ) ∂unitaryHaar n) +
          ∫ k : unitaryCompact ℂ n, f (k : Langlands.GeneralLinear n ℂ) *
            rightDerivative (matrixModel ℂ n) X h (k : Langlands.GeneralLinear n ℂ)
              ∂unitaryHaar n = 0

/-- `ComplexStandardDualityStatement` follows from the `𝔤`-invariance of the integral over
`U(n)`, with the integration pairing. -/
theorem complexStandardDuality_of_lieInvariance (hLie : IntegralLieInvariance) :
    ComplexStandardDualityStatement := by
  intro n ds ds' hχ
  refine ⟨integralPairing n (complexPositionCharacter ds) (complexPositionCharacter ds'),
    fun k f h hf hh => integralPairing_rightTranslation _ _ k f h hf hh,
    fun X f h hf hh => ?_, fun h h0 => ?_⟩
  · rw [integralPairing_apply, integralPairing_apply]
    exact hLie n _ _ hχ f h (Submodule.mem_inf.mp f.2).1 (Submodule.mem_inf.mp h.2).1 X
  · obtain ⟨s, hs⟩ := exists_normSq_complexPositionCharacter ds
    obtain ⟨f, hf⟩ := exists_integral_mul_ne_zero hχ hs h h0
    exact ⟨f, hf⟩

end Langlands.Archimedean.ComplexDuality
