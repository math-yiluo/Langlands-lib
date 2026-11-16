import Langlands.Representation.Archimedean.StandardModule

/-!
# An uncertainty principle for the two block rotations of `O(3)`

`r_0(θ) = blockRotation 3 0 θ` rotates the coordinates `0, 1` of `ℝ³` and `r_1(θ) =
blockRotation 3 1 θ` the coordinates `1, 2`; they are the rotations about two orthogonal axes.
For a function `f` on `GL_3(ℝ)` the block Fourier coefficients
`blockFourierCoefficient 3 p j f g = ∫₀^{2π} f(r_p(θ) g) e^{-ijθ} dθ` measure the left Fourier
modes of `f` along `r_p`.

`RealOrthogonalBlockUncertaintyStatement` says: a continuous right `O(3)`-finite function whose
left Fourier modes along one of the two rotations are all at least `n` in absolute value, and
whose left Fourier modes along the other rotation are all smaller than `n'` in absolute value,
vanishes on `O(3)` when `n' < n`. The statement is only stated here.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

/-- **Statement (uncertainty principle for two block rotations of `O(3)`).** Let `{p, q} =
{0, 1}`, let `n' < n` be natural numbers, and let `f : GL_3(ℝ) → ℂ` be continuous and right
`O(3)`-finite. Suppose that, at every `g ∈ O(3)`, the left Fourier coefficients
`∫₀^{2π} f(r_p(θ) g) e^{-ijθ} dθ` vanish for `|j| < n` and the left Fourier coefficients
`∫₀^{2π} f(r_q(θ) g) e^{-ijθ} dθ` vanish for `|j| ≥ n'`. Then `f` vanishes on `O(3)`. -/
def RealOrthogonalBlockUncertaintyStatement : Prop :=
  ∀ (p q n n' : ℕ) (f : Langlands.GeneralLinear 3 ℝ → ℂ),
    (p = 0 ∧ q = 1 ∨ p = 1 ∧ q = 0) → n' < n → Continuous f →
    f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear 3 ℝ))
      (unitaryCompact ℝ 3) →
    (∀ g ∈ unitaryCompact ℝ 3, ∀ j : ℤ, |j| < (n : ℤ) →
      blockFourierCoefficient 3 p j f g = 0) →
    (∀ g ∈ unitaryCompact ℝ 3, ∀ j : ℤ, (n' : ℤ) ≤ |j| →
      blockFourierCoefficient 3 q j f g = 0) →
    ∀ g ∈ unitaryCompact ℝ 3, f g = 0

end Langlands.Archimedean
