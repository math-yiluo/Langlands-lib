import Langlands.Representation.Aubert.HeadProductLeadingTerm
import Langlands.Representation.Aubert.HeadProductLeadingTermStatement

/-! # Proof of the head-product leading-term statement -/

noncomputable section

namespace Langlands.Aubert

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- **Head-product leading term.** For products of actual Langlands heads,
constituent heads satisfy the multisegment rank bound, the head of the sum
multisegment has composition multiplicity one, and a different constituent
head below a uniform-length sum contains a longer segment. -/
theorem headProductLeadingTerm : HeadProductLeadingTermStatement.{uF, uV} F T := by
  intro m n dA dB dC A B C hA hB hC
  exact ⟨HeadProductLeadingTerm.rankLE_of_isSubquotient F T dA dB dC A B C hA hB hC,
    fun hmult hfin => HeadProductLeadingTerm.compositionMultiplicity_eq_one F T dA dB dC hmult
      A B C hA hB hC hfin,
    fun _l hsub hlen hne => HeadProductLeadingTerm.exists_longer_segment_of_isSubquotient F T
      dA dB dC A B C hA hB hC hsub hlen hne⟩

end Langlands.Aubert
