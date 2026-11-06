# Algebraic ingredients for connected integral lattice reflection

Author: Worker 1584.

These internal lemmas provide the algebra needed by the connected reflection
proof. Multiplication by a globally invertible positive integer is a published
isogeny. Its cancellation property implies injectivity of positive integer
multiplication on actual Hom groups. Rational equality is equality after a
nonzero integer multiple; passing to its positive absolute value then proves
injectivity of actual Hom rationalization.

Positive denominators are constructed directly by induction on the rational
tensor product: a pure tensor uses its rational coefficient's positive
denominator, and sums use products of denominators. This avoids an intermediate
choice of a signed denominator.

Finally, a multiplication isogeny is surjective on points over an algebraically
closed field. Every section therefore has roots of every positive order, so the
factorial-tower lemma in `FullSeparation` gives surjectivity of every full Tate
projection at the specified geometric point. These are derived lemmas about the
published constructions, not additional assumptions on the target.
