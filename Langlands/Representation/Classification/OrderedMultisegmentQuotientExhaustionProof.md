# Ordered special-segment quotient coverage

Authors: Worker 963 and Worker 391 of the previous instance. The latter supplied
the carried conditional assembly; Worker 963 discharged its refinement premise
using the published proof and prepared the exact unconditional theorem.

`Langlands.Classification.orderedMultisegmentQuotientExhaustion` proves exactly
`Langlands.Classification.OrderedMultisegmentQuotientExhaustion.{uF,uV} F T`.
Its outer telescope is `{p : Nat} [Fact p.Prime]`,
`(F : PadicField.{uF} p)`, and `(T : F.TopologicalData)`.
The field and carrier universe parameters remain independent.

For every natural rank `n` and every irreducible smooth complex representation
`π` of `GL_n(F)` in the saturated carrier universe `max uF uV`, the theorem
constructs an actual `d : T.SegmentProductDatum.{max uF uV,uF} n`
satisfying `d.IsLanglandsQuotient π`. The datum contains the equality of its
segment-degree sum with `n`. Its segments are nonprecedence ordered, its
actual blocks satisfy the strong individual segment-head relations, and its
normalized upper product has an actual surjective intertwiner onto the
given input `π`. No admissibility premise is added.

The proof splits on `n`.

- In rank zero, it applies the published
  [`zeroRankMultisegmentQuotientExhaustion`](ZeroRankMultisegmentQuotientProof.md).
  That proof supplies a datum with empty segment and block families and the
  actual empty-product quotient map. It identifies the induced carrier with
  the complex scalar line and uses irreducibility of the input to make the
  resulting nonzero intertwiner surjective.
- In positive rank, the published
  [`temperedLanglandsQuotientCoverage`](TemperedLanglandsQuotientCoverageProof.md)
  supplies an actual tempered Langlands datum `t` and an irreducible quotient
  relation from `t.standardModule` onto the original `π`. The published
  [`temperedSpecialSegmentRefinement`](TemperedSpecialSegmentRefinementProof.md)
  then supplies the ordered segment datum `d`, its strong individual heads,
  and an actual smooth isomorphism `e : d.induced ≅ t.standardModule`.
  Applying `IsIrreducibleQuotient.of_equiv` to the inverse of
  `SmoothRep.equivOfIso e` transports the source of the quotient relation.
  Concretely, it composes the quotient map with the forward isomorphism from
  `d.induced` to `t.standardModule`, preserving surjectivity and the original
  target representation. The ordering and individual heads come directly
  from refinement.

All three input theorems are closed published proofs. Both positive-rank
theorems are instantiated at `.{uF,uV}`, matching the target's saturated
carriers. The products keep the existing upper block parabolic, positive
half-modulus covariance, and right translation conventions.

This is an internal composition of published Library results, with provenance
and implementations documented in the linked proof pairs. The combined project
import closure was checked against the published base: it uses no downstream
multisegment head exhaustion, square-integrable exhaustion, or regular
exhaustion proof. The target pair and its imported pairs are unchanged.
Full-product quotient-kernel uniqueness is outside this coverage conclusion;
the strong head condition here concerns each individual segment block.
