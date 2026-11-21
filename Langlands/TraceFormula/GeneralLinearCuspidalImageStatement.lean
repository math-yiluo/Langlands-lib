import Langlands.Automorphic.ConstantTerm
import Langlands.Global.FiniteAdelicGL.LocalFactor
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Convolution with a test function that is cuspidal at one finite place

Let `K` be a number field, `μ` a left Haar measure on `GL_n(𝔸_K)` and `v` a finite place of `K`.
Suppose that `f : GL_n(𝔸_K) → ℂ` is continuous with compact support. For every split
`a + b = n` with `a, b ≥ 1`, assume that the integral

`∫ f(x · ι_v([[1, Z], [0, 1]]) · y) dZ`

vanishes for all `x, y ∈ GL_n(𝔸_K)` and every additive Haar measure `dZ` on `a × b`
matrices over `K_v` with the Borel σ-algebra. Here `ι_v` inserts a local matrix at `v`
and the identity elsewhere.

For every left `GL_n(K)`-invariant, locally integrable `φ`, the convolution
`R(f)φ(x) = ∫ f(g) φ(x g) dμ(g)` is continuous, left `GL_n(K)`-invariant and cuspidal
in the sense of `Langlands.Automorphic.IsCuspidal`. Compactness of `𝔸_K / K` is an
instance parameter.

This formulation is derived from Getz–Hahn 2024, Definition 16.4.1 and Lemma 16.4.2
(printed p. 430). See `GeneralLinearCuspidalImageStatement.md`.
-/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory
open Langlands.Global Langlands.Automorphic Langlands.GeneralLinear

universe u

/-- If `f` is continuous with compact support on `GL_n(𝔸_K)` and its integrals over the
upper block unipotent subgroups of `GL_n(K_v)`, at one finite place `v`, vanish for every
two-sided translate, then for every left `GL_n(K)`-invariant locally integrable `φ` the
function `x ↦ ∫ f(g) φ(x g) dμ(g)` is a continuous rational-left-invariant function that is
cuspidal (all constant terms along standard maximal block parabolics vanish). -/
def GeneralLinearCuspidalImageStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] [CompactSpace (AdeleQuotient K)] (n : ℕ)
    [MeasurableSpace (AdelicGL K n)] [BorelSpace (AdelicGL K n)]
    (μ : Measure (AdelicGL K n)) [μ.IsHaarMeasure]
    (v : FinitePlace K) (f : AdelicGL K n → ℂ), Continuous f → HasCompactSupport f →
    (∀ (a b : ℕ) (h : a + b = n), 0 < a → 0 < b →
      letI : MeasurableSpace (Matrix (Fin a) (Fin b) (FiniteCompletion K v)) := borel _
      ∀ ν : Measure (Matrix (Fin a) (Fin b) (FiniteCompletion K v)), ν.IsAddHaarMeasure →
        ∀ x y : AdelicGL K n,
          ∫ Z, f (x * AdelicGL.ofFinite K n
            (FiniteAdelicGL.localInclusion K n v (blockUnipotent h Z)) * y) ∂ν = 0) →
    ∀ φ : AdelicGL K n → ℂ, (∀ (γ : RationalGL K n) (x : AdelicGL K n),
        φ (AdelicGL.rational K n γ * x) = φ x) → LocallyIntegrable φ μ →
    ∃ F : ContinuousRationalFunctions K n,
      (∀ x, ContinuousRationalFunctions.evaluate K n F x = ∫ g, f g * φ (x * g) ∂μ) ∧
        IsCuspidal K n F

end Langlands.TraceFormula
