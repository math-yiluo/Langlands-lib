import Langlands.Global.Factors.CuspidalPairEisensteinPartialOpenCell
import Langlands.Global.RankinSelberg.UnequalAnalyticStatement

/-! # The semilocal numerator of the open-cell integral

Every finite set of finite places is contained in a finite set `S₀` such that for every point
`s₀` of the imaginary axis there is a section, spherical outside `S₀`, whose partial open-cell
integral over the adelic matrices integral outside `S₀` is, on a right half-plane, a
meromorphic function regular and nonzero at `s₀`. This is the part of the proof of Shahidi
(1981), Theorem 5.1, pp. 351–352, at the places of `S₀` and the archimedean places, with
Propositions 3.1 and 3.2, pp. 332–333. See the paired Markdown. -/

set_option autoImplicit false

universe u

namespace Langlands.Global

open NumberField CuspidalPairEisenstein
open Automorphic (CuspidalOperatorRealization)
open RankinSelbergGlobal (IsStandardAdditiveCharacter)
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

/-- For actual cuspidal realizations `T`, `T'` with unitary central characters, a standard
additive character `ψ` and a finite set `S` of finite places, there is a finite set
`S₀ ⊇ S` such that for every `s₀` with `Re s₀ = 0` there are a section `φ` built from cusp forms
spherical outside `S₀` and a function `c`, meromorphic on `ℂ`, analytic and nonzero at `s₀`, with
`c s = I_(S₀)(φ, s)` on a right half-plane, where `I_(S₀)` is the partial open-cell integral
over the matrices integral outside `S₀`. -/
def CuspidalPairEisensteinSemilocalNumeratorStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    HasUnitaryCentralCharacter T → HasUnitaryCentralCharacter T' →
  ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
  ∀ S : Finset (FinitePlace F),
  ∃ S₀ : Finset (FinitePlace F), S ⊆ S₀ ∧
    ∀ s₀ : ℂ, s₀.re = 0 →
      ∃ φ : AdelicGL F (r + t + 2) → ℂ, IsSection T T' φ ∧ IsSphericalSectionOutside T T' S₀ φ ∧
        ∃ c : ℂ → ℂ, MeromorphicOn c Set.univ ∧ AnalyticAt ℂ c s₀ ∧ c s₀ ≠ 0 ∧
          ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → c s = partialOpenCellIntegral ψ S₀ φ s

end Langlands.Global
