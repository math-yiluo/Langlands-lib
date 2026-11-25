# Cofinal whole-space Steinberg irreducibility from supplied root coordinates

This internal module proves the exact cofinal whole-space seventh-law formula
for the polarized-rho dynamic subgroup and its negative-rho coordinate from
an explicit split pinning, integral coroot span, and
`SimpleRootCoordinateFamily`. The algebraically closed field has prime
exponential characteristic `q`. No highest-weight existence or irreducibility
premise is added. The supplied structural data remain required, so this is
not the unconditional Steinberg big-cell target.

`suppliedRhoSteinbergBasis` chooses a finite standard-indexed basis of the
entire covariant coordinate space using the supplied-family same-height
detection theorem. Given any desired exponent, the elementary prime-power
bound chooses a positive height `r` with larger Steinberg exponent `q^r - 1`.
The Library's dominant highest-weight existence theorem supplies a module
of that weight. The supplied-family whole-space height theorem makes
the regular representation of the chosen whole-space basis irreducible.
These witnesses give exactly the cofinal exponent, finite basis and rational
irreducibility required by law 7.

The numerical height bound and specialization of highest-weight existence
are generic Library adapters. The chosen basis uses the supplied-family
finite-dimensionality result, not the canonical basis construction
`canonicalRhoSteinbergBasis`.
The highest-weight existence proof uses a generic opposite dynamic cell,
Levi characters, realized weights and covariant socles. It uses ordinary
Borel quotient properness transitively through maximal-torus centralizers,
reductivity of dynamic centralizers and the Chevalley unipotent envelope:
`unipotentTorusBorelsToAllBorels` applies `someBorelQuotientProper`.
The implemented route avoids the regular-cocharacter identification of a
dynamic subgroup as Borel and the canonical-rho Borel/big-cell assembly. This is derived internal
content and adds no external source claim.
