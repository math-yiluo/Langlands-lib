import Langlands.Representation.Classification.SpehNeighborRectangleLengthBound
import Langlands.Representation.Aubert.HeadProductLeadingTermProof
import Langlands.Representation.Classification.MoeglinWaldspurgerAubertCorrectnessProof

/-! # Irreducibility of u(δ,k+1) × u(δ,k−1) for Speh representations

Badulescu (2014), Theorem 1(b)(ii): for a discrete series δ and `k ≥ 2`, the normalized
product of the Speh representations `u(δ,k+1)` and `u(δ,k−1)` is irreducible. The proof
combines the published Moeglin–Waldspurger Aubert correctness theorem and the published
head-product leading-term theorem with the rectangle length bound and reduction of this
development. -/

noncomputable section

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The target from universal Moeglin–Waldspurger Aubert correctness, using the
published head-product leading-term theorem. -/
theorem spehNeighborProductIrreducibility_of_universalAubertCorrectness
    (hMW : MoeglinWaldspurger.UniversalAubertCorrectness.{uF, max uF uV}) :
    SpehNeighborProductIrreducibility.{uF, uV} F T :=
  SpehNeighborProduct.spehNeighborProductIrreducibility_of_rectangle_bound F T
    (Aubert.headProductLeadingTerm F T)
    (SpehNeighborProduct.neighborRectangleConstituentLengthBound_of_aubertCorrectness F T
      (hMW p F T) (Aubert.headProductLeadingTerm F T))

/-- **Badulescu (2014), Theorem 1(b)(ii).** For a discrete series δ and `k ≥ 2`, the
normalized product `u(δ,k+1) × u(δ,k−1)` of Speh representations is irreducible. -/
theorem spehNeighborProductIrreducibility :
    SpehNeighborProductIrreducibility.{uF, uV} F T :=
  spehNeighborProductIrreducibility_of_universalAubertCorrectness F T
    MoeglinWaldspurger.universalAubertCorrectness.{uF, max uF uV}

end Langlands.Classification
