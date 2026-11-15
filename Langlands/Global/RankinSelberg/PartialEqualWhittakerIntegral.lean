import Langlands.Global.RankinSelberg.PartialWhittakerIntegrals
import Langlands.Global.RankinSelberg.EqualIntegrals

/-! # The partial equal-rank global Whittaker integral

The integral `Ψ_(S∪∞)(s; W, W', Φ)`: the equal-rank global Whittaker integral
`Ψ(s; W, W', Φ) = ∫_(N_n(𝔸) \ GL_n(𝔸)) W(g) W'(g) Φ(e_n g) |det g|^s dg` restricted to the
classes of the points `g` with `g_v ∈ N_n(F_v) GL_n(𝒪_v)` at every finite place `v ∉ S`.
See the paired Markdown for sources and normalizations.
-/

noncomputable section
universe u
open NumberField MeasureTheory
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

variable (F : Type u) [Field F] [NumberField F]

/-- The partial equal-rank Whittaker integral `Ψ_(S∪∞)(s; W, W', Φ)`: the integral
`equalWhittakerIntegral` restricted to the classes `N_n(𝔸) g` whose representative
satisfies `g_v ∈ N_n(F_v) GL_n(𝒪_v)` at every finite place `v ∉ S`, with the same
quotient measure. -/
def partialEqualWhittakerIntegral {r : ℕ} (S : Finset (FinitePlace F))
    (W W' : Points F (r + 1) → ℂ) (Φ : RowVector F (r + 1) → ℂ) (s : ℂ) : ℂ :=
  ∫ q in {q : WhittakerQuotient F (r + 1) | q.out ∈ unipotentIntegralOutside F (r + 1) S},
    equalWhittakerIntegrand F W W' Φ s q ∂whittakerQuotientMeasure F (r + 1)

end Langlands.Global.RankinSelbergGlobal
