# Exact rank-one cell calculus over commutative rings

This is an internal derivation from the group laws, actual root equivariance,
uniqueness of open-cell coordinates, and supplied normalizer data. It generalizes
the algebraic parts of `RankOneRootCellRelation` and `RankOneRootCellWeyl` from
fields to arbitrary commutative rings. No literature assertion is added.

`RingRootCell.CellData` consists of actual group schemes, a map from a commutative
group scheme, two additive-group maps of weights alpha and minus alpha, and the
open immersion of their negative-root/torus/positive-root multiplication.
The elementary point identities, naturality, uniqueness of coordinates, and
open-cell membership and descent along maps surjective on underlying points
are proved directly, over every test scheme. Splitness, maximality and even the
torus property of the commutative group are unnecessary for this calculation.

`reflectionIso` uses the actual character-cocharacter composite equal to twice
the identity; it does not infer this equality from field fibres. `WeylData`
adds this cocharacter, a supplied actual normalizer with that reflection action,
a torus-valued square, and a supplied decomposition of xp(1)n in the cell with
unit negative and positive coordinates beta and delta. Neither this decomposition
nor this normalizer is constructed here.

The calculation first establishes equivariance of xp(c squared)n, pulls back
the supplied decomposition, and compares two such cell expressions. When delta
is a square of a unit, uniqueness of coordinates and the torus-valued square of
n imply alpha(gamma) times delta equals minus one. Subtracting two positive
coordinates then gives `relation_of_unit_squares`: for units w and u with
u = 1 + Xw, xp(X)xm(beta w) equals xm(beta u inverse w)h(u)xp(u inverse X),
provided square roots of delta, w inverse and u w inverse are supplied. This
argument uses ring identities and unit inverses, retaining nilpotents and all
residue characteristics. It currently requires those square roots explicitly.
The arbitrary-ring host Isomorphism Theorem remains open.
