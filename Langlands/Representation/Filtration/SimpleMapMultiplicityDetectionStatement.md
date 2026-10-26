# Positive multiplicity detection by nonzero simple maps

This is an internal derived statement interface for actual finite
composition-series multiplicities. It is not a translation of a new external
source and does not assert its own proof.

`JordanHolderSubobjectSimpleMapDetectionStatement` works over an arbitrary
field `k` and monoid `G`. It takes representations `A`, `B`, and an irreducible
test representation `τ`, an actual injective intertwiner `i : B → A`, and an
actual finite composition-series witness counting `τ` in `A` exactly `M`
times. If either an actual map `τ → B` or an actual map `B → τ` is nonzero,
it asserts the existence of an actual finite composition-series witness
counting `τ` in `B` exactly `m` times, where `0 < m` and `m ≤ M`.

`JordanHolderQuotientSimpleMapDetectionStatement` has the same conclusion
for an actual surjective intertwiner `q : A → B`. In both clauses either
direction of the nonzero simple map is permitted, independently of the
direction of the ambient map. The five universes for `k`, `G`, `A`, `B`,
and `τ` remain independent. No topology, admissibility, semisimplicity,
or finite-dimensionality hypothesis is imposed. The actual-series witness
for `A` is essential; the statement does not manufacture finite length from
a nonzero map alone.

`JordanHolderSimpleMapDetectionStatement` is the conjunction of these two
claims. Here “subobject” and “quotient” refer to the supplied actual injective
and surjective maps; the conclusions keep actual composition series through
`HasJordanHolderMultiplicity`.

The derivation is motivated by the existing Library's actual short-exact
multiplicity decomposition and monotonicity statements and its one-factor
series for an irreducible representation. The ambient finite series first
supplies a series for `B` through the range or kernel short exact sequence.
A nonzero map out of the simple `τ` is injective, and a nonzero map into `τ`
is surjective. In either case the self-count one of `τ` is bounded by the
count in `B`. This describes the intended algebraic justification; an exact
proof is a separate publication obligation.

The interface imports only the generic representation filtration definitions.
It has no GL, induction, Jacquet, segment, or analytic classification
dependency. In particular it supplies only a conditional multiplicity
detector for the segment existence task: construction of the ambient
multiplicity witness, the actual ambient map, and the nonzero simple map
remains outside its scope.
