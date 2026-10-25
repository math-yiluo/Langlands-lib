# Rank-zero ordered special-segment quotient coverage

Author: Worker 19.

`Langlands.Classification.ZeroRankMultisegmentQuotientExhaustion.{uF,uV}`
is the rank-zero specialization of
`Langlands.Classification.OrderedMultisegmentQuotientExhaustion`, imported
from `MultisegmentQuotientExhaustionStatement`. It is an internal
proof-decomposition target: its provenance is precisely the parent
proposition with `n = 0`. This module supplies a proposition-valued definition
and no proof, and makes no separate literature-based rank-zero claim.

The outer parameters are exactly `{p : Nat} [Fact p.Prime]`,
`F : PadicField.{uF} p` and `T : F.TopologicalData`. With `T.topology`
installed, the proposition quantifies every
`π : SmoothRep.{0,uF,max uF uV} Complex (GeneralLinear 0 F.Carrier)`.
Its only premise on `π` is `Representation.IsIrreducible π.representation`.
It asks for an actual
`d : T.SegmentProductDatum.{max uF uV,uF} 0` with
`d.IsLanglandsQuotient π`. The field universe `uF` and carrier parameter `uV`
remain independent. The given representation `π` remains the target of the
quotient map. There is no admissibility or classification premise.

The imported relation retains all three clauses from `LanglandsData`:

- No earlier segment precedes a later segment.
- Every block satisfies the strong individual `IsSegmentHead` relation,
  including equality of kernels of irreducible quotient maps of that segment's
  induced representation.
- There is an actual surjective intertwiner from `d.induced.representation`
  to `π.representation`, which is irreducible.

Full-product kernel uniqueness is not part of this quotient relation.

Each segment has strictly positive degree by `Segment.degree_pos` in
`Segments`: its degree is the product of its positive length and positive
cuspidal rank. The datum's `degree_sum` says that the sum of these degrees
is zero. If its length were positive, one positive summand would make the
sum positive. Thus any witness has length zero, and the ordering and
individual-head conditions are vacuous.

The induced representation still uses the existing
`normalizedProductInductionFunctor` on the datum's empty block shape.
In particular, its block tensor is the empty `PiTensorProduct` over `Complex`,
followed by normalized induction from the standard upper block parabolic.
This preserves the parent's empty-product normalization. The finite tensor
product over no factors has the scalar field as its tensor unit; implementing
the corresponding equivalence and the evaluation identification for induction
on the trivial group `GL₀(F)` is part of a later proof. That proof must also
relate the resulting scalar representation to the actual irreducible `π`
and supply the required surjective intertwiner. The empty product is not
definitionally the arbitrary input representation, and the empty segment
family alone does not discharge this obligation.
