import Langlands.Global.RankinSelberg.PartialEqualWhittakerIntegral
import Langlands.Global.RankinSelberg.EqualUnfoldingStatement
import Langlands.Global.Factors.CuspidalPairBoundaryNonvanishingStatement
import Langlands.Global.Factors.RelativeGammaComparisonStatement
import Langlands.Automorphic.Contragredient

/-! # Partial Euler factorization of the equal-rank dual global Whittaker integral

Cogdell 2004, §2.3, pp.210–211, and §4.1, proof of Theorem 4.1, pp.219–220, with
Theorem 3.3, p.215. See the paired Markdown for sources, normalizations and the comparison
with the Library's unramified factors.
-/

noncomputable section
universe u uQ
open NumberField MeasureTheory
open Langlands.Global.CuspidalPairBoundaryNonvanishing
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance equalDualEulerSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalDualEulerSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- **Cogdell 2004, pp.210–211 and 219–220, with Theorem 3.3, p.215**: partial Euler
factorization of the equal-rank dual global Whittaker integral.

Let `ψ`, `T`, `T'` (both of rank `n = r + 1`) and `S` be as in
`EqualEulerFactorizationStatement`, and let `Td`, `Td'` be actual cuspidal realizations of
the contragredients of `T`, `T'`, with spectral presentations `Pd`, `Pd'` whose exceptional
sets lie in `S`. Then there is `σ` such that for all vectors `x`, `x'` fixed by
`GL_n(𝒪_v)` at every finite `v ∉ S` and every `Φ ∈ S(𝔸^n)` equal to `1_(𝒪_v^n)` at every
finite `v ∉ S`, with `W̃ = W_x(w_n ᵗg⁻¹)`, `W̃' = W'_x'(w_n ᵗg⁻¹)` and `Φ̂` the Fourier
transform of `Φ` for `ψ`, and every `s` with `σ < Re s`: the global Whittaker integral
`Ψ(s; W̃, W̃', Φ̂)` converges absolutely, the Euler product of the unramified contragredient
pair factors `L(s, Π̃_v × Π̃'_v)` over the finite `v ∉ S` converges absolutely, and
`Ψ(s; W̃, W̃', Φ̂) = Ψ_(S∪∞)(s; W̃, W̃', Φ̂) · ∏_(v ∉ S) L(s, Π̃_v × Π̃'_v)`. -/
def EqualDualEulerFactorizationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T Td T' Td' : Automorphic.CuspidalOperatorRealization F r),
    Automorphic.OperatorRealization.IsContragredientOf Td.realization T.realization →
    Automorphic.OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (Pd : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td)
    (Pd' : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td')
    (S : Finset (FinitePlace F)) (hPd : Pd.exceptional ⊆ S) (hPd' : Pd'.exceptional ⊆ S),
    FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
    ∃ σ : ℝ, ∀ (x : T.Space) (x' : T'.Space) (Φ : RowVector F (r + 1) → ℂ),
      IsSphericalOutside F T S x → IsSphericalOutside F T' S x' →
      Φ ∈ schwartzBruhat F (r + 1) → IsStandardOutside F (r + 1) S Φ →
      let Wdual := dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x)
      let W'dual := dualFunction F (r + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')
      let Φhat := fourierTransform F (r + 1) ψ.complex Φ
      ∀ s : ℂ, σ < s.re →
        Integrable (equalWhittakerIntegrand F Wdual W'dual Φhat s)
          (whittakerQuotientMeasure F (r + 1)) ∧
        Summable (fun v => ‖partialEulerFactor Pd Pd' hPd hPd' v s - 1‖) ∧
        ∃ p : ℂ, HasProd (fun v => partialEulerFactor Pd Pd' hPd hPd' v s) p ∧
          equalWhittakerIntegral F Wdual W'dual Φhat s =
            partialEqualWhittakerIntegral F S Wdual W'dual Φhat s * p

end Langlands.Global.RankinSelbergGlobal
