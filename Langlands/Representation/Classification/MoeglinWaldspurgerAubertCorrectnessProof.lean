import Langlands.Representation.Classification.MoeglinWaldspurgerConditionalCorrectness
import Langlands.Representation.Classification.LanglandsSubrepresentationProof
import Langlands.Representation.Classification.LeftCuspidalDerivativeProof

/-!
# Aubert correctness of the Moeglin–Waldspurger multisegment recursion

The conditional theorem `Derivation.universalAubertCorrectness_of_interfaces` applied to the
Library proofs of `LeftCuspidalDerivativeLemma` and `LanglandsSubrepresentationRealization`.
-/

noncomputable section

namespace Langlands.MoeglinWaldspurger

open Langlands.Classification Langlands.Classification.LeftCuspidalDerivative

universe uF uV

/-- Aubert correctness from the left cuspidal derivative lemma alone. -/
theorem universalAubertCorrectness_of_leftCuspidalDerivativeLemma
    (hL : LeftCuspidalDerivativeLemma.{uF, uV}) :
    UniversalAubertCorrectness.{uF, uV} :=
  Derivation.universalAubertCorrectness_of_interfaces hL
    langlandsSubrepresentationRealization.{uF, uV}

/-- **Aubert correctness of the Moeglin–Waldspurger multisegment recursion.** For every prime
`p`, actual `p`-adic field `F` with topological data `T`, cuspidal datum `ρ`, real shift `x` and
multisegment `a`, the support-adjusted Aubert operator sends the class of the Langlands head of
`realize ρ x a` to the class of the Langlands head of `realize ρ x (dual a)`. -/
theorem universalAubertCorrectness : UniversalAubertCorrectness.{uF, uV} :=
  universalAubertCorrectness_of_leftCuspidalDerivativeLemma leftCuspidalDerivativeLemma.{uF, uV}

end Langlands.MoeglinWaldspurger
