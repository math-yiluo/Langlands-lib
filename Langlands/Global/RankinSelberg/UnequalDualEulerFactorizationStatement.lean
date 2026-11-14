import Langlands.Global.RankinSelberg.PartialWhittakerIntegrals
import Langlands.Global.RankinSelberg.UnequalUnfoldingStatement
import Langlands.Global.Factors.CuspidalPairBoundaryNonvanishingStatement
import Langlands.Global.Factors.RelativeGammaComparisonStatement
import Langlands.Automorphic.Contragredient

/-! # Partial Euler factorization of the unequal-rank dual global Whittaker integrals

Cogdell 2004, §4.1, proof of Theorem 4.1, p.220, with Theorems 3.2 and 3.3, pp.214–215.
See the paired Markdown for sources, normalizations and the comparison with the
Library's unramified factors.
-/

noncomputable section
universe u uQ
open NumberField MeasureTheory
open Langlands.Global.CuspidalPairBoundaryNonvanishing
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance dualEulerSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance dualEulerSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- **Cogdell 2004, p.220, with Theorems 3.2–3.3, pp.214–215**: partial Euler
factorization of the unequal-rank dual global Whittaker integral.

Let `ψ`, `T`, `T'`, `t < r` and `S` be as in `UnequalEulerFactorizationStatement`, and let
`Td`, `Td'` be actual cuspidal realizations of the contragredients of `T`, `T'`, with
spectral presentations `Pd`, `Pd'` whose exceptional sets lie in `S`. Then there is `σ`
such that for all vectors `x`, `x'` fixed by `GL(𝒪_v)` at every finite `v ∉ S`, with
`W̃ = W_x(w_n ᵗg⁻¹)` translated on the right by `w_(n,m) = diag(I_m, w_(n-m))` and
`W̃' = W'_x'(w_m ᵗg⁻¹)`, and every `s` with `σ < Re s`: the iterated dual integral
converges absolutely, the Euler product of the unramified contragredient pair factors
`L(s, Π̃_v × Π̃'_v)` over the finite `v ∉ S` converges absolutely, and
`Ψ̃(s; ρ(w_(n,m)) W̃, W̃') = Ψ̃_(S∪∞)(s; ρ(w_(n,m)) W̃, W̃') · ∏_(v ∉ S) L(s, Π̃_v × Π̃'_v)`. -/
def UnequalDualEulerFactorizationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r t : ℕ) (h : t < r)
    (T Td : Automorphic.CuspidalOperatorRealization F r)
    (T' Td' : Automorphic.CuspidalOperatorRealization F t),
    Automorphic.OperatorRealization.IsContragredientOf Td.realization T.realization →
    Automorphic.OperatorRealization.IsContragredientOf Td'.realization T'.realization →
  ∀ (Pd : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td)
    (Pd' : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td')
    (S : Finset (FinitePlace F)) (hPd : Pd.exceptional ⊆ S) (hPd' : Pd'.exceptional ⊆ S),
    FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
    ∃ σ : ℝ, ∀ (x : T.Space) (x' : T'.Space),
      IsSphericalOutside F T S x → IsSphericalOutside F T' S x' →
      let Wdual := translateFunction F (r + 1) (unfoldingWeyl F h)
        (dualFunction F (r + 1) (cuspWhittaker F T ψ.complex x))
      let W'dual := dualFunction F (t + 1) (cuspWhittaker F T' ψ.complex⁻¹ x')
      ∀ s : ℂ, σ < s.re →
        DualWhittakerAbsolutelyConvergent F h Wdual W'dual s ∧
        Summable (fun v => ‖partialEulerFactor Pd Pd' hPd hPd' v s - 1‖) ∧
        ∃ p : ℂ, HasProd (fun v => partialEulerFactor Pd Pd' hPd hPd' v s) p ∧
          dualWhittakerIntegral F h Wdual W'dual s =
            partialDualWhittakerIntegral F h S Wdual W'dual s * p

end Langlands.Global.RankinSelbergGlobal
