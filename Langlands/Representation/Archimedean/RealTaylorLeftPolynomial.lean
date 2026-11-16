import Langlands.Representation.Archimedean.RealLeftPolynomialGrowth

/-!
# A Taylor condition on `O(n)` making principal-series functions polynomial along a root group

Let `p + 1 < n`, `E = E_{p+1,p}` (`lowerRootMatrix`) and `e(t) = 1 + t E` (`lowerRootElement`).
Let `χ` be characters of `ℝˣ` with `χ_{p+1}(x) = x^k χ_p(x)` for `x > 0`, and `h` a function of
the smooth principal series `principalSeries ℝ n χ` of `GL_n(ℝ)`.

`RealTaylorLeftPolynomialStatement`: if the `k`-th derivative `d^k/dt^k h(e(t) κ)` at `t = 0`
vanishes for every `κ ∈ O(n)`, then `t ↦ h(e(t) g)` is a polynomial of degree `< k` for every
`g ∈ GL_n(ℝ)`.

The `k`-th derivative at `t = 0` of `t ↦ h(e(t) κ)` is written as the `k`-th iterated right
derivative along `E` at the identity of the right translate of `h` by `κ`.
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

/-- **Taylor condition on `O(n)` and polynomiality along a lower root group.** Let `χ` be
functions `ℝˣ → ℂ` indexed by positions, `p + 1 < n` and `k : ℕ` with
`χ_{p+1}(x) = x^k χ_p(x)` for every `x > 0`. Let `h` lie in the smooth principal series
`principalSeries ℝ n χ` of `GL_n(ℝ)`, and suppose that for every `κ ∈ O(n)` the `k`-fold
iterated right derivative along `E_{p+1,p}`, taken at the identity, of the right translate
`g ↦ h(g κ)` vanishes; that is, `d^k/dt^k h(e(t) κ) = 0` at `t = 0`, where
`e(t) = 1 + t E_{p+1,p}`. Then for every `g ∈ GL_n(ℝ)` there is a complex polynomial `q` of
degree `< k` with `h(e(t) g) = q(t)` for all real `t`. -/
def RealTaylorLeftPolynomialStatement : Prop :=
  ∀ (n : ℕ) (χ : ℕ → ℝˣ → ℂ) (p k : ℕ) (hp : p + 1 < n),
    (∀ x : ℝˣ, 0 < (x : ℝ) → χ (p + 1) x = ((x : ℝ) : ℂ) ^ k * χ p x) →
    ∀ h ∈ principalSeries ℝ n χ,
      (∀ κ ∈ unitaryCompact ℝ n,
        (rightDerivative (matrixModel ℝ n) (lowerRootMatrix n p hp))^[k]
          (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) κ h) 1 = 0) →
      ∀ g : Langlands.GeneralLinear n ℝ, ∃ q : Polynomial ℂ, q.degree < k ∧
        ∀ t : ℝ, h (lowerRootElement n p hp t * g) = q.eval (t : ℂ)

end Langlands.Archimedean
