# Positive characters on independent cocharacters

Worker 1633. The theorem
`Langlands.GroupScheme.positiveCharacterOnIndependentCocharacters.{u,v}`
proves the whole proposition
`Langlands.GroupScheme.PositiveCharacterOnIndependentCocharactersStatement.{u,v}`.
This is the positive-character lattice prerequisite of the coefficientwise
moderate-growth argument.

The generic helper first identifies the integral lattice with finitely many
integer coordinates. Integer linear independence remains independence after
embedding all coordinates into the rationals. The independent vectors form a
basis of their rational span. Giving that basis any prescribed integer
values defines a rational functional on the span, and `Subspace.dualLift`
extends it to the full coordinate space.

For each of the finitely many standard coordinate vectors, the functional
has a rational value. A common nonzero integer denominator `b` makes those
values integral. Multiplying their integer numerators once more by `b`
produces an integer dot-product functional whose values equal `b²` times
the prescribed values. The multiplier is strictly positive. This is the
same elementary finite denominator-clearing method used, for the dual
character-to-cocharacter direction, in the published
`Rational.IndependentStandardCocharacter` module. No unpublished draft is
used.

The second generic helper applies this coordinate result to a chosen basis
of any finite free integer module. The index type of the independent family
has its own universe, and the helper does not require it to be finite.

For the torus theorem, `IsSplitTorus.exists_cocharacterCoordinates` identifies
the actual cocharacter lattice with a finite coordinate lattice. Apply the
generic helper with all prescribed values equal to one.
`IsSplitTorus.isPerfPair_latticePairing` is surjective onto the integral dual,
so the resulting integral functional is the pairing with an actual
character of the given torus. Each required pairing equals the common
positive integer `b²`.

The proof includes empty families, the rank-zero torus, every field
characteristic, and independent field and family universes. It proves no
cone decomposition, norm estimate, or coefficientwise growth assertion.

The declaration-level inputs are
`IsSplitTorus.exists_cocharacterCoordinates` from
`Rational.SplitTorusIsogenyCocharacterLinear`,
`IsSplitTorus.isPerfPair_latticePairing` from `Absolute.RegularPerturbation`,
and Mathlib's `linearIndependent_algebraMap_comp_iff`,
`Module.Basis.span`, `Subspace.dualLift`,
`IsLocalization.exist_integer_multiples_of_finite`, and `dotProductEquiv`.
The finite-free wrapper additionally uses `Module.Free.chooseBasis`.
The proof is an internal derivation from these published algebraic
constructions; it invokes no representation-theoretic growth theorem.
