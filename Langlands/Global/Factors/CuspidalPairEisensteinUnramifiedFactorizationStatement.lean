import Langlands.Global.Factors.CuspidalPairEisensteinPartialOpenCell
import Langlands.Global.RankinSelberg.PartialEulerProductConvergence
import Langlands.Global.Factors.RelativeGammaComparisonStatement

/-! # Unramified factorization of the open-cell integral

For a section spherical outside a finite set `S` of finite places, the open-cell integral of
a cuspidal-pair Eisenstein series, multiplied by the partial Euler product
`L^S(1 + s, π × π')`, is the partial open-cell integral over the adelic matrices that are
integral outside `S`, on a right half-plane. This is the unramified part of the proof of
Shahidi (1981), Theorem 5.1, pp. 351–352, with the local value of Casselman–Shalika (1980),
Theorem 5.4. See the paired Markdown. -/

set_option autoImplicit false

universe u uQ

namespace Langlands.Global

open MeasureTheory NumberField CuspidalPairBoundaryNonvanishing CuspidalPairEisenstein
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)
open RankinSelbergGlobal (partialEulerProduct)
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

/-- For actual cuspidal realizations `T`, `T'` with unitary central characters, spectral
presentations `P`, `P'` of `T`, `T'` and `Pd` of the contragredient realization
`dualRealization T'`, a unitary character `ψ` of `𝔸` trivial on `F`, and a finite set `S` of
finite places containing the three exceptional sets and outside which every finite component
of `ψ` has conductor `𝒪_v`: for every section `φ` built from cusp forms spherical outside `S`
there is `σ` such that for
`σ < Re s`, if the open-cell integrand is integrable, then
`L^S(1 + s, π × π') · I(φ, s) = I_S(φ, s)`, where `I_S` is the partial open-cell integral over
the matrices integral outside `S`. -/
def CuspidalPairEisensteinUnramifiedFactorizationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    HasUnitaryCentralCharacter T → HasUnitaryCentralCharacter T' →
  ∀ (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (Pd : CuspidalSpectralPresentation.{u, uQ} (dualRealization T'))
    (S : Finset (FinitePlace F)) (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S),
    Pd.exceptional ⊆ S →
  ∀ (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
    FunctionalEquationComparison.FiniteAdditiveSupport ψ S →
  ∀ φ : AdelicGL F (r + t + 2) → ℂ, IsSection T T' φ → IsSphericalSectionOutside T T' S φ →
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      (letI : MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) := borel _;
        Integrable (openCellIntegrand ψ.complex φ s) (openCellHaar F r t)) →
      partialEulerProduct P P' hP hP' (1 + s) * openCellIntegral ψ.complex φ s =
        partialOpenCellIntegral ψ.complex S φ s

end Langlands.Global
