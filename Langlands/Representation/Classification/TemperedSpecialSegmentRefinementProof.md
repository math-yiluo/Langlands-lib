# Tempered Langlands data refined into ordered special segments

Author: Worker 627.

`Langlands.Classification.temperedSpecialSegmentRefinement` proves exactly
`Langlands.Classification.TemperedSpecialSegmentRefinement.{uF,uV} F T`.
Its outer telescope is `{p : Nat} [Fact p.Prime]`,
`(F : PadicField.{uF} p)`, and `(T : F.TopologicalData)`.
The field and carrier universe parameters are independent.

For every positive rank `n` and actual
`t : T.TemperedLanglandsDatum.{max uF uV,uF} n`, the theorem supplies an actual
`d : T.SegmentProductDatum.{max uF uV,uF} n` with `d.IsPrecedenceOrdered`,
`d.HasSegmentHeads`, and `Nonempty (d.induced ≅ t.standardModule)`.
The strong head relations include uniqueness of each irreducible quotient
kernel. The degree sum and the isomorphism concern actual smooth complex
representations. Both products use the existing normalized upper block
induction, with positive half-modulus covariance and right translation.

The Lean proof applies the published
[refinement assembly](TemperedSpecialSegmentRefinementAssembly.md) to four
closed published proofs:

| Proof | Role and universe specialization |
| --- | --- |
| [`temperedBlockExhaustion`](TemperedBlockExhaustionProof.md) | Exhaust each untwisted tempered parent block by actual irreducible square-integrable unitarizable factors; use `.{uF,uV}`. |
| [`segmentEssentialSquareIntegrableClassification`](SegmentEssentialSquareIntegrableClassificationProof.md) | Identify every twisted factor with a strong special-segment head at its actual rank; use `.{uF,uV}`. |
| [`linkedSegmentHeadExponentComparison`](LinkedSegmentHeadExponentProof.md) | Segment precedence forces strictly increasing exponents for the supplied head normalizations; use `.{uF,uV}`. |
| [`Parabolic.orderedProductRegrouping`](../Parabolic/OrderedProductRegroupingProof.md) | Flatten consecutive normalized products with their coordinate and rank transports; use `.{uF,max uF uV}`. |

The assembly exhausts the untwisted factors before applying the parent's real
determinant twist. Its twist and rank transports give every refined head a
unitary exponent equal to that parent's exponent. Consecutive flattening keeps
the parent indices weakly increasing. A preceding pair would therefore have
strictly increasing head exponents, contradicting equality within a parent or
the decreasing parent exponents. This supplies global nonprecedence, including
pairs from the same parent. The assembly retains the individual strong heads
and actual degree equalities, and composes the regrouping isomorphism with the
inner twisted-factor isomorphisms to obtain `d.induced ≅ t.standardModule`.
Square-integrability and invariant positive forms are used on the untwisted
factors; the argument does not assert their preservation by arbitrary real
twists.

All four premises are discharged in this theorem. There is no additional
analytic or classification hypothesis, arbitrary irreducible input, assumed
factorization, or full-product quotient condition. Saturating regrouping at
`max uF uV` keeps all representation carriers in the exact universe required
by the unchanged target.

This is an internal composition of the linked Library proofs, whose paired
documentation records their implementations and provenance. No new direct
literature reading or source theorem is claimed here. The proof remains
upstream of ordered special-segment quotient coverage, multisegment exhaustion,
square-integrable exhaustion, and regular exhaustion; none is used as a proof
input. The target pair and its imported pairs are unchanged.
