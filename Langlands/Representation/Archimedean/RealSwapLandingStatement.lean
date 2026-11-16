import Langlands.Representation.Archimedean.StandardModule
import Langlands.Representation.Archimedean.RealBlockMultiplier

/-!
# Landing of composites of block Fourier multipliers on `GL_3(ℝ)`

Let `c` be a real character data and `d` a complex character data of weight `m`, `ℓ = |m|`.
The standard module of `[d, c]` on `GL_3(ℝ)` consists of principal-series functions whose left
Fourier modes along the rotations `r_0(θ) = blockRotation 3 0 θ` (coordinates `0, 1`) are at
least `ℓ` in absolute value; the standard module of `[c, d]` has the same condition along
`r_1(θ) = blockRotation 3 1 θ` (coordinates `1, 2`).

A block Fourier multiplier along `r_p` multiplies the left Fourier coefficient of weight `k`
along `r_p` by a scalar `μ k`. The two statements of this module say that, on `O(3)`, the
composite of a multiplier along one rotation followed by a multiplier along the other, both
solving the recurrence of `RealBlockMultiplier.IsRecurrent` for parameters `δ` and `δ + ℓ`
and symmetric with the sign `(-1)^ε` of their parity class `ε`, carries the `O(3)`-finite
functions of one standard module to functions whose modes along the other rotation are at
least `ℓ` in absolute value:

* `RealSwapLandingInducedFirstStatement`: from `[d, c]`, first along `r_1`, then along `r_0`;
* `RealSwapLandingCharacterFirstStatement`: from `[c, d]`, first along `r_0`, then along `r_1`;
* `RealSwapLandingStatement`: both.

The parameter `δ` is arbitrary: it is not tied to the exponents of `c` and `d`. Everything is
only stated here.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean RealBlockMultiplier

/-- **Statement (landing from `[d, c]`).** Let `c` be a real character data of parity `ε₁`,
`d` a complex character data of weight `m`, `ℓ = |m|`, and `ε₀ = ℓ + 1 + ε₁`. Let `δ ∈ ℂ`, let
`μ₁` solve the recurrence for `δ` on the parity class `ε₁` with symmetry sign `(-1)^ε₁`, and
`μ₀` the recurrence for `δ + ℓ` on the class `ε₀` with sign `(-1)^ε₀`. Let `f` be an
`O(3)`-finite function of the standard module of `[d, c]` on `GL_3(ℝ)`, and let `h`, `u` be
continuous functions with, at every point of `O(3)`, the left Fourier coefficients
`Φ¹_k h = μ₁ k · Φ¹_k f` along `r_1` and `Φ⁰_k u = μ₀ k · Φ⁰_k h` along `r_0`. Then the left
Fourier coefficients `Φ¹_k u` along `r_1` vanish on `O(3)` for `|k| < ℓ`. -/
def RealSwapLandingInducedFirstStatement : Prop :=
  ∀ (c : RealCharacterData) (d : ComplexCharacterData) (δ : ℂ) (μ₀ μ₁ : ℤ → ℂ)
    (f h u : Langlands.GeneralLinear 3 ℝ → ℂ),
    IsRecurrent δ (c.parity.val : ℤ) μ₁ →
    IsSymmetric (c.parity.val : ℤ) ((-1 : ℂ) ^ c.parity.val) μ₁ →
    IsRecurrent (δ + (d.weight.natAbs : ℂ)) ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ) μ₀ →
    IsSymmetric ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ)
      ((-1 : ℂ) ^ (d.weight.natAbs + 1 + c.parity.val)) μ₀ →
    f ∈ kFiniteFunctions (realStandardModule 3 [RealBlock.induced d, RealBlock.character c])
      (unitaryCompact ℝ 3) →
    Continuous h → Continuous u →
    (∀ g ∈ unitaryCompact ℝ 3, ∀ k : ℤ,
      blockFourierCoefficient 3 1 k h g = μ₁ k * blockFourierCoefficient 3 1 k f g) →
    (∀ g ∈ unitaryCompact ℝ 3, ∀ k : ℤ,
      blockFourierCoefficient 3 0 k u g = μ₀ k * blockFourierCoefficient 3 0 k h g) →
    ∀ g ∈ unitaryCompact ℝ 3, ∀ k : ℤ, |k| < |d.weight| →
      blockFourierCoefficient 3 1 k u g = 0

/-- **Statement (landing from `[c, d]`).** Let `c`, `d`, `ℓ`, `ε₁`, `ε₀` be as in
`RealSwapLandingInducedFirstStatement`. Let `δ ∈ ℂ`, let `μ₀` solve the recurrence for `δ` on
the parity class `ε₀` with symmetry sign `(-1)^ε₀`, and `μ₁` the recurrence for `δ + ℓ` on the
class `ε₁` with sign `(-1)^ε₁`. Let `f` be an `O(3)`-finite function of the standard module of
`[c, d]` on `GL_3(ℝ)`, and let `h`, `u` be continuous functions with, at every point of
`O(3)`, `Φ⁰_k h = μ₀ k · Φ⁰_k f` along `r_0` and `Φ¹_k u = μ₁ k · Φ¹_k h` along `r_1`. Then
the left Fourier coefficients `Φ⁰_k u` along `r_0` vanish on `O(3)` for `|k| < ℓ`. -/
def RealSwapLandingCharacterFirstStatement : Prop :=
  ∀ (c : RealCharacterData) (d : ComplexCharacterData) (δ : ℂ) (μ₀ μ₁ : ℤ → ℂ)
    (f h u : Langlands.GeneralLinear 3 ℝ → ℂ),
    IsRecurrent δ ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ) μ₀ →
    IsSymmetric ((d.weight.natAbs + 1 + c.parity.val : ℕ) : ℤ)
      ((-1 : ℂ) ^ (d.weight.natAbs + 1 + c.parity.val)) μ₀ →
    IsRecurrent (δ + (d.weight.natAbs : ℂ)) (c.parity.val : ℤ) μ₁ →
    IsSymmetric (c.parity.val : ℤ) ((-1 : ℂ) ^ c.parity.val) μ₁ →
    f ∈ kFiniteFunctions (realStandardModule 3 [RealBlock.character c, RealBlock.induced d])
      (unitaryCompact ℝ 3) →
    Continuous h → Continuous u →
    (∀ g ∈ unitaryCompact ℝ 3, ∀ k : ℤ,
      blockFourierCoefficient 3 0 k h g = μ₀ k * blockFourierCoefficient 3 0 k f g) →
    (∀ g ∈ unitaryCompact ℝ 3, ∀ k : ℤ,
      blockFourierCoefficient 3 1 k u g = μ₁ k * blockFourierCoefficient 3 1 k h g) →
    ∀ g ∈ unitaryCompact ℝ 3, ∀ k : ℤ, |k| < |d.weight| →
      blockFourierCoefficient 3 0 k u g = 0

/-- **Statement (landing of block multiplier composites on `GL_3(ℝ)`).** Both
`RealSwapLandingInducedFirstStatement` and `RealSwapLandingCharacterFirstStatement`. -/
def RealSwapLandingStatement : Prop :=
  RealSwapLandingInducedFirstStatement ∧ RealSwapLandingCharacterFirstStatement

end Langlands.Archimedean
