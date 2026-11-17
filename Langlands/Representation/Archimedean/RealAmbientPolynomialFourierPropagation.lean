import Langlands.Representation.Archimedean.RealPolynomialFourierPropagation
import Langlands.Representation.Archimedean.RealAmbientOrthogonalUncertainty

/-! # Polynomial Fourier propagation in arbitrary ambient rank -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealAmbientPolynomialFourierPropagation

open Polynomial RealOrthogonalBlock RealBlockFrobeniusMap RealBlockMultiplier
open RealTailMultiplierPolynomial RealStandardFiltration RealBlockJacquet
open Langlands.LocalFactor.Archimedean

theorem propagation {n : ℕ} (a : ℕ) (ha : a + 3 ≤ n) {r s : ℕ}
    (hrs : s = 0 ∧ r = 1 ∨ s = 1 ∧ r = 0)
    {f g : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g)
    (hfK : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n))
    (hgK : g ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n))
    (Q : ℂ[X])
    (hμ : ∀ j : ℤ, ∀ x ∈ unitaryCompact ℝ n,
      blockFourierCoefficient n (a + r) j g x =
        Q.eval (j : ℂ) * blockFourierCoefficient n (a + r) j f x)
    (cutoff : ℕ)
    (hlow : ∀ x ∈ unitaryCompact ℝ n, ∀ j : ℤ, (cutoff : ℤ) ≤ |j| →
      blockFourierCoefficient n (a + s) j f x = 0) :
    ∀ x ∈ unitaryCompact ℝ n, ∀ j : ℤ,
      ((cutoff + Q.natDegree : ℕ) : ℤ) ≤ |j| →
      blockFourierCoefficient n (a + s) j g x = 0 := by
  have hr : r + 1 < 3 := by rcases hrs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  have hs : s + 1 < 3 := by rcases hrs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
  intro x hx j hj
  have hlocal := RealPolynomialFourierPropagation.propagation hrs
    (continuous_restrictCoset a ha x hf) (continuous_restrictCoset a ha x hg)
    (restrictCoset_mem_kFiniteVectors a ha hx hfK)
    (restrictCoset_mem_kFiniteVectors a ha hx hgK) Q
    (fun m k hk => by
      rw [blockFourierCoefficient_restrictCoset a ha hr,
        blockFourierCoefficient_restrictCoset a ha hr]
      exact hμ m _ ((unitaryCompact ℝ n).mul_mem
        (block_mem_unitaryCompact a ha hk) hx))
    cutoff (fun k hk m hm => by
      rw [blockFourierCoefficient_restrictCoset a ha hs]
      exact hlow _ ((unitaryCompact ℝ n).mul_mem
        (block_mem_unitaryCompact a ha hk) hx) m hm)
  have hz := hlocal 1 (one_mem _) j hj
  rw [blockFourierCoefficient_restrictCoset a ha hs] at hz
  simpa only [map_one, one_mul] using hz

/-- Actual tail Frobenius maps have the same propagation bound in each adjacent ambient window. -/
theorem tail_propagation {n : ℕ} (a : ℕ) (ha : a + 3 ≤ n) {r s ℓ : ℕ} {ε : ℤ}
    {ds es : List RealBlock}
    (hrs : s = 0 ∧ r = 1 ∨ s = 1 ∧ r = 0)
    (h : IsBlockFrobData n ds es (a + r) ε ((-1 : ℂ) ^ ℓ)
      (tailMultiplier ℓ ε ((-1 : ℂ) ^ ℓ)))
    (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1) (hpar : Even ((ℓ : ℤ) - 1 - ε))
    (f : KF n ds) (cutoff : ℕ)
    (hlow : ∀ x ∈ unitaryCompact ℝ n, ∀ j : ℤ, (cutoff : ℤ) ≤ |j| →
      blockFourierCoefficient n (a + s) j f x = 0) :
    ∀ x ∈ unitaryCompact ℝ n, ∀ j : ℤ, ((cutoff + ℓ : ℕ) : ℤ) ≤ |j| →
      blockFourierCoefficient n (a + s) j (blockFrobMap h f) x = 0 := by
  have hμ : ∀ j : ℤ, ∀ x ∈ unitaryCompact ℝ n,
      blockFourierCoefficient n (a + r) j (blockFrobMap h f) x =
        (tailPolynomial ℓ).eval (j : ℂ) *
          blockFourierCoefficient n (a + r) j f x := by
    intro j x hx
    rw [blockFourierCoefficient_blockFrobMap h f hx]
    by_cases hj : Even (j - ε)
    · rw [tailPolynomial_eq hℓ hε hpar j hj]
    · rw [blockFourierCoefficient_eq_zero_of_not_even h.lt h.par f hj x, mul_zero, mul_zero]
  simpa only [tailPolynomial_natDegree] using
    propagation a ha hrs (continuous_coe f) (continuous_coe (blockFrobMap h f))
      f.2.2 (blockFrobMap h f).2.2 (tailPolynomial ℓ) hμ cutoff hlow

end Langlands.Archimedean.RealAmbientPolynomialFourierPropagation

namespace Langlands.Archimedean

open Polynomial in
/-- Polynomial Fourier multipliers propagate adjacent cutoffs in every ambient rank. -/
def RealAmbientPolynomialFourierPropagationStatement : Prop :=
  ∀ (n a : ℕ), a + 3 ≤ n →
  ∀ (r s : ℕ), (s = 0 ∧ r = 1 ∨ s = 1 ∧ r = 0) →
  ∀ f g : Langlands.GeneralLinear n ℝ → ℂ, Continuous f → Continuous g →
    f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n) →
    g ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ))
      (unitaryCompact ℝ n) →
  ∀ Q : ℂ[X],
    (∀ j : ℤ, ∀ x ∈ unitaryCompact ℝ n,
      blockFourierCoefficient n (a + r) j g x =
        Q.eval (j : ℂ) * blockFourierCoefficient n (a + r) j f x) →
  ∀ cutoff : ℕ,
    (∀ x ∈ unitaryCompact ℝ n, ∀ j : ℤ, (cutoff : ℤ) ≤ |j| →
      blockFourierCoefficient n (a + s) j f x = 0) →
    ∀ x ∈ unitaryCompact ℝ n, ∀ j : ℤ,
      ((cutoff + Q.natDegree : ℕ) : ℤ) ≤ |j| →
      blockFourierCoefficient n (a + s) j g x = 0

theorem realAmbientPolynomialFourierPropagation :
    RealAmbientPolynomialFourierPropagationStatement := by
  intro n a ha r s hrs f g hf hg hfK hgK Q hμ cutoff hlow
  exact RealAmbientPolynomialFourierPropagation.propagation a ha hrs hf hg hfK hgK Q hμ cutoff hlow

end Langlands.Archimedean
