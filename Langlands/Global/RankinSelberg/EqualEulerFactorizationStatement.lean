import Langlands.Global.RankinSelberg.PartialEqualWhittakerIntegral
import Langlands.Global.Factors.CuspidalPairBoundaryNonvanishingStatement
import Langlands.Global.Factors.RelativeGammaComparisonStatement

/-! # Partial Euler factorization of the equal-rank global Whittaker integral

Cogdell 2004, §2.3, p.210, with Theorem 3.3, p.215. See the paired Markdown for sources,
normalizations and the comparison with the Library's unramified factors.
-/

noncomputable section
universe u uQ
open NumberField MeasureTheory
open Langlands.Global.CuspidalPairBoundaryNonvanishing
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance equalEulerSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalEulerSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- **Cogdell 2004, §2.3, p.210, with Theorem 3.3, p.215**: partial Euler factorization
of the equal-rank global Whittaker integral.

Let `ψ` be a nontrivial unitary character of `𝔸` trivial on `F`, let `T`, `T'` be actual
cuspidal realizations of `GL_(r+1)` with spectral presentations `P`, `P'`, and let `S` be a
finite set of finite places containing both exceptional sets and outside which every
finite component of `ψ` has conductor `𝒪_v`. Then there is `σ` such that for all vectors
`x`, `x'` fixed by `GL(𝒪_v)` at every finite `v ∉ S`, every `Φ ∈ S(𝔸^n)` equal to
`1_(𝒪_v^n)` at every finite `v ∉ S`, with `W = W_x` the `ψ`-Whittaker function and
`W' = W'_x'` the `ψ⁻¹`-Whittaker function, and every `s` with `σ < Re s`: the global
Whittaker integral converges absolutely, the Euler product of the unramified pair factors
`L(s, Π_v × Π'_v)` over the finite `v ∉ S` converges absolutely, and
`Ψ(s; W, W', Φ) = Ψ_(S∪∞)(s; W, W', Φ) · ∏_(v ∉ S) L(s, Π_v × Π'_v)`. -/
def EqualEulerFactorizationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T T' : Automorphic.CuspidalOperatorRealization F r)
    (P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T)
    (P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T')
    (S : Finset (FinitePlace F)) (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S),
    FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
    ∃ σ : ℝ, ∀ (x : T.Space) (x' : T'.Space) (Φ : RowVector F (r + 1) → ℂ),
      IsSphericalOutside F T S x → IsSphericalOutside F T' S x' →
      Φ ∈ schwartzBruhat F (r + 1) → IsStandardOutside F (r + 1) S Φ →
      let W := cuspWhittaker F T ψ.complex x
      let W' := cuspWhittaker F T' ψ.complex⁻¹ x'
      ∀ s : ℂ, σ < s.re →
        Integrable (equalWhittakerIntegrand F W W' Φ s)
          (whittakerQuotientMeasure F (r + 1)) ∧
        Summable (fun v => ‖partialEulerFactor P P' hP hP' v s - 1‖) ∧
        ∃ p : ℂ, HasProd (fun v => partialEulerFactor P P' hP hP' v s) p ∧
          equalWhittakerIntegral F W W' Φ s =
            partialEqualWhittakerIntegral F S W W' Φ s * p

end Langlands.Global.RankinSelbergGlobal
