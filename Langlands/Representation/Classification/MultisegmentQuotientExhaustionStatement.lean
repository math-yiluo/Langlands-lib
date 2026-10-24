import Langlands.Representation.Classification.LanglandsData

/-!
# Ordered special-segment quotient coverage

This proposition isolates the existence of an ordered special-segment product
surjecting onto a given irreducible representation. Uniqueness of the quotient
kernel of the whole product is not part of this assertion.
-/

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every irreducible smooth representation is an actual quotient of some
nonprecedence-ordered product of special segment heads. This is the coverage
part of multisegment head exhaustion, with full-product kernel uniqueness
omitted. The statement includes rank zero. -/
def OrderedMultisegmentQuotientExhaustion : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
    Representation.IsIrreducible π.representation →
      ∃ d : T.SegmentProductDatum.{max uF uV, uF} n, d.IsLanglandsQuotient π

end Langlands.Classification
