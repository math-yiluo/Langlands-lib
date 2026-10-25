import Langlands.Representation.Classification.MultisegmentQuotientExhaustionStatement

/-!
# Rank-zero ordered special-segment quotient coverage

The rank-zero specialization of `OrderedMultisegmentQuotientExhaustion`.
This module states the actual quotient obligation for the empty segment product.
-/

namespace Langlands.Classification

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every irreducible smooth representation of `GL₀(F)` is an actual quotient
of a precedence-ordered product of special segment heads. Positive segment
degrees force this product to have no segments. -/
def ZeroRankMultisegmentQuotientExhaustion : Prop :=
  letI := T.topology
  ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 0 F.Carrier)),
    Representation.IsIrreducible π.representation →
      ∃ d : T.SegmentProductDatum.{max uF uV, uF} 0, d.IsLanglandsQuotient π

end Langlands.Classification
