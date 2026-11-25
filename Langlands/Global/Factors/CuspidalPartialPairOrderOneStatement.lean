import Langlands.Global.Factors.CuspidalPairBoundaryNonvanishingStatement
import Langlands.Automorphic.Contragredient

/-! # Order at one of the partial cuspidal pair L-function

The order at `s = 1` in Arthur–Clozel III.2 (2.2)–(2.3), with Shahidi's
nonvanishing, on the Library's supplied meromorphic partial pair functions.
-/

noncomputable section

universe u uQ

set_option autoImplicit false

namespace Langlands.Global

open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation OperatorRealization)
open CuspidalPairBoundaryNonvanishing (IsPartialPairLFunction)
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

/-- The partial pair L-function of two unitary cusps has a simple pole at one in
the contragredient case and order zero otherwise. -/
def CuspidalPartialPairOrderOneStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    HasUnitaryCentralCharacter T → HasUnitaryCentralCharacter T' →
    ∀ (P : CuspidalSpectralPresentation.{u, uQ} T)
      (P' : CuspidalSpectralPresentation.{u, uQ} T')
      (S : Finset (FinitePlace F)) (hP : P.exceptional ⊆ S) (hP' : P'.exceptional ⊆ S)
      (L : ℂ → ℂ), IsPartialPairLFunction P P' hP hP' L →
      let isDual := ∃ hrt : r = t,
        OperatorRealization.IsContragredientOf (n := t + 1) (hrt ▸ T.realization) T'.realization
      (isDual → meromorphicOrderAt L 1 = -1) ∧
        (¬ isDual → meromorphicOrderAt L 1 = 0)

end Langlands.Global
