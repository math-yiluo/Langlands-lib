# Segment duality reverses precedence

Worker 1816 derived these helpers for the proof of multisegment constituent compatibility. They concern the published endpoint-reversed segment dual, not a new choice of segment constituents.

An integral coordinate interval `[a,b]` for a segment becomes `[-b,-a]` on the dual cuspidal line. The proof expands the segment dual and uses the published law that cuspidal duality negates real twists. The positive segment length justifies the natural-number subtraction in the last endpoint.

The published integral-coordinate criterion expresses precedence by the endpoint inequalities `a < c`, `c ≤ b + 1`, and `b < d`. Negating and reversing endpoints preserves these inequalities in reversed order. The proof uses the proved integral twist freeness for actual supercuspidal classes; no freeness hypothesis is added. Applying segment duality twice gives the converse.

The mathematical content is an internal consequence of `SegmentHeadContragredient`, `SegmentIntervalLinkage`, and `CuspidalIntegralTwistFreenessProof`. It supports the reversed ordering required in the existing multisegment compatibility statement.
