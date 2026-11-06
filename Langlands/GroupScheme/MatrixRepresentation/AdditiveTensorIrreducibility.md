# Actual tensor irreducibility from additive coefficient fullness

This internal derived unit uses actual matrix representations and the previously
proved coefficient-algebra separation theorem. It works over a field in arbitrary
universe `u`, with an arbitrary index family in universe `v` and finite decidable
coordinate types in `Type`.

`invariantAlgebra W` consists of all matrices preserving a specified subspace
`W` of the full coordinate space. Containment of a supplied additive family's
coefficient algebra in this preserving algebra is equivalent to stability under
each actual additive representation on every affine test algebra. This uses
the published universal polynomial coefficient extraction, including nonreduced
test algebras; no infinitude or characteristic hypothesis is needed here.

If that family coefficient algebra is the full matrix algebra, every common
stable subspace is zero or the entire original coordinate space. The proof
takes a nonzero vector in a nonzero subspace, chooses one nonzero coordinate,
and constructs a matrix sending that vector to any prescribed vector.

For an actual representation of any supplied ambient group scheme, stability
restricts along every supplied additive-group morphism. Consequently full
coefficient algebra of those restrictions implies the existing all-test
`MatrixRepresentation.IsIrreducible` predicate, provided the coordinate type is
nonempty. No density or group-generation hypothesis is required for this
sufficient condition.

In prime characteristic `p`, the final theorem applies this criterion to the
actual common-source tensor `ρ.tensor (σ.frobeniusPower p e)`. Its hypotheses
are fullness of the first restriction family's coefficients below `p^e` and
fullness of the actual Frobenius-powered second restriction family's coefficient
algebra. The earlier separation theorem supplies full tensor coefficient algebra.
The actual restriction compatibilities for tensor and Frobenius identify this
family with the restrictions of the original ambient tensor representation.
The conclusion concerns its entire product-coordinate space.

Both fullness hypotheses remain substantive inputs. This unit does not derive
them from restrictedness, construct a generating root family or a Steinberg
representation, or prove the general `SteinbergBigCellStatement`. It assumes no
first-factor degree bound, perfectness, algebraic closedness or infinitude.
