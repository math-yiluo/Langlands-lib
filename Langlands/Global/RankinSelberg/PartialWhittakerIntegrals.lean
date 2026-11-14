import Langlands.Global.RankinSelberg.WhittakerIntegrals
import Langlands.Global.FiniteAdelicGL.LocalFactor

/-! # Unramified-place data for the global Rankin–Selberg Euler factorization

The local component of an actual adelic point at a finite place, the subset
`N_n(F_v) GL_n(𝒪_v)` of the local group, adelic points lying in it at every finite
place outside a finite set `S`, vectors of an actual cuspidal realization fixed by
`GL_n(𝒪_v)` at every finite place outside `S`, and the partial unequal-rank ordinary and
dual Whittaker integrals `Ψ_(S∪∞)`, `Ψ̃_(S∪∞)`. See the paired Markdown for sources and
normalizations.
-/

noncomputable section
universe u
open NumberField MeasureTheory
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

variable (F : Type u) [Field F] [NumberField F]

/-- The component `g_v ∈ GL_n(F_v)` at a finite place `v` of an actual adelic point `g`. -/
def finiteComponent (n : ℕ) (v : FinitePlace F) (g : Points F n) : FiniteLocalGL F n v :=
  FiniteAdelicGL.localProjection F n v
    (AdelicGL.finite F n (GeneralLinearGroupPoints.adelicEquiv F n g))

/-- `x ∈ N_n(F_v) GL_n(𝒪_v)`: some right multiple of `x` by an element of
`GL_n(𝒪_v)` is upper unitriangular. -/
def IsUnipotentIntegral (n : ℕ) (v : FinitePlace F) (x : FiniteLocalGL F n v) : Prop :=
  ∃ k ∈ FiniteAdelicGL.localIntegral F n v,
    (∀ i, (x * k) i i = 1) ∧ ∀ i j, j < i → (x * k) i j = 0

/-- Adelic points `g` with `g_v ∈ N_n(F_v) GL_n(𝒪_v)` at every finite place `v ∉ S`.
No condition is imposed at the places of `S` or at the infinite places. -/
def unipotentIntegralOutside (n : ℕ) (S : Finset (FinitePlace F)) : Set (Points F n) :=
  {g | ∀ v ∉ S, IsUnipotentIntegral F n v (finiteComponent F n v g)}

/-- The vector `x` of an actual cuspidal realization of `GL_(r+1)` is fixed by
`GL_(r+1)(𝒪_v)`, acting through the finite adelic action at the place `v`, for every
finite place `v ∉ S`. -/
def IsSphericalOutside [CompactSpace (AdeleQuotient F)] {r : ℕ}
    (T : Automorphic.CuspidalOperatorRealization F r) (S : Finset (FinitePlace F))
    (x : T.Space) : Prop :=
  ∀ v ∉ S, ∀ k ∈ FiniteAdelicGL.localIntegral F (r + 1) v,
    T.realization.finiteRepresentation (FiniteAdelicGL.localInclusion F (r + 1) v k) x = x

/-- The partial unequal-rank Whittaker integral `Ψ_(S∪∞)(s; W, W')`: the integral
`unequalWhittakerIntegral` restricted to the classes `N_m(𝔸) h` whose representative
satisfies `h_v ∈ N_m(F_v) GL_m(𝒪_v)` at every finite place `v ∉ S`, with the same
quotient measure. -/
def partialUnequalWhittakerIntegral {r t : ℕ} (h : t < r) (S : Finset (FinitePlace F))
    (W : Points F (r + 1) → ℂ) (W' : Points F (t + 1) → ℂ) (s : ℂ) : ℂ :=
  ∫ q in {q : WhittakerQuotient F (t + 1) | q.out ∈ unipotentIntegralOutside F (t + 1) S},
    unequalWhittakerIntegrand F h W W' s q ∂whittakerQuotientMeasure F (t + 1)

/-- The partial dual Whittaker integral `Ψ̃_(S∪∞)(s; W, W')`: the outer integral of
`dualWhittakerIntegral` restricted to the classes `N_m(𝔸) h` whose representative
satisfies `h_v ∈ N_m(F_v) GL_m(𝒪_v)` at every finite place `v ∉ S`. The inner integral
over `M_(n-m-1,m)(𝔸)` is unchanged. -/
def partialDualWhittakerIntegral {r t : ℕ} (h : t < r) (S : Finset (FinitePlace F))
    (W : Points F (r + 1) → ℂ) (W' : Points F (t + 1) → ℂ) (s : ℂ) : ℂ :=
  ∫ q in {q : WhittakerQuotient F (t + 1) | q.out ∈ unipotentIntegralOutside F (t + 1) S},
    dualWhittakerIntegrand F h W W' s q ∂whittakerQuotientMeasure F (t + 1)

end Langlands.Global.RankinSelbergGlobal
