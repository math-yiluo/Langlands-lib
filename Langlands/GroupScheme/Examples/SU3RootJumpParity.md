# Indivisible central jumps in normalized quadratic coordinates

These internal coordinate arguments combine the exact jump
characterizations with published ramified quadratic valuation arithmetic.
`Parameters.HasIndivisibleCentralJump` means that some real central jump has its
half absent from the ordinary quotient jump set. This condition and the first
trace-zero characterization apply to any field with a ring involution and an
additive valuation into `WithTop ℝ`. The subsequent arithmetic results concern a
separable quadratic field extension `L/K` and a conjugation-invariant valuation
of `L`.

A central jump is equivalently a real value attained by a nonzero trace-zero
second coordinate. In the normalized ramified case, assume that all nonzero
base-field scalars have integer values and some extension element has value
`1/2`, as in `IsRamifiedQuadraticValuation`. The published trace-zero parity
lemma places each central jump in `ℤ + 1/2 + μ`, while nonzero extension values
are half-integers. The quotient jump formula places twice each quotient jump in
`ℤ + μ`. Thus the half of a central jump cannot be a quotient jump: an integer
cannot equal an integer plus `1/2`. A nonzero trace-zero element supplies a
central jump, proving existence of a central jump whose half is absent.

For the integer-valued case, assume instead that every nonzero element of `L`
has integer valuation, and that an embedded `K` scalar has value one. The
valuation inequality bounds trace-one values above by zero. The greatest
bounded integer principle and separability give an attained maximum. A nonzero
trace-zero element and its product by the value-one base scalar supply two
central jumps differing by one. If both halves were quotient jumps, the exact
quotient formula would make their difference twice an integer, contradicting
that it is one. At least one central jump therefore has no quotient half-jump.

No restriction is made on field characteristic, residue characteristic or
residue perfection. These results concern normalized coordinate valuations;
normalizing a general finite tower and comparing with actual apartment roots
are not asserted here.
