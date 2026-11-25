import Langlands.Global.Factors.CuspidalPairBoundaryNonvanishingStatement
import Langlands.Global.Factors.CuspidalPairEisensteinSeries
import Langlands.Global.RankinSelberg.UnequalAnalyticStatement

/-! # Shahidi's generic Fourier-coefficient identity for a cuspidal pair -/

set_option autoImplicit false

universe u uQ

namespace Langlands.Global

open NumberField CuspidalPairBoundaryNonvanishing CuspidalPairEisenstein
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)
open RankinSelbergGlobal (IsStandardAdditiveCharacter)
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

/-- The identity in the proof of Shahidi (1981), Theorem 5.1, specialized to the
upper two-block parabolic of `GL_(r+t+2)`. A single enlargement of the omitted set
works for all imaginary parameters. At each such parameter there is a section with
regular, nonzero numerator in the Fourier-coefficient identity. -/
def CuspidalPairEisensteinCoefficientStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    HasUnitaryCentralCharacter T → HasUnitaryCentralCharacter T' →
  ∀ (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (S : Finset (FinitePlace F)) (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
    (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
  ∃ (S₀ : Finset (FinitePlace F)) (hS : S ⊆ S₀),
    ∀ s₀ : ℂ, s₀.re = 0 →
      ∃ φ, IsSection T T' φ ∧
        ∃ c : ℂ → ℂ, MeromorphicOn c Set.univ ∧ AnalyticAt ℂ c s₀ ∧ c s₀ ≠ 0 ∧
          ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
            Summable (fun v =>
              ‖partialEulerFactor P P' (hP.trans hS) (hP'.trans hS) v (1 + s) - 1‖) ∧
            ∃ Λ : ℂ,
              HasProd (fun v => partialEulerFactor P P' (hP.trans hS) (hP'.trans hS) v (1 + s)) Λ ∧
              c s = Λ * coeff (r := r) (t := t) ψ φ s

end Langlands.Global
