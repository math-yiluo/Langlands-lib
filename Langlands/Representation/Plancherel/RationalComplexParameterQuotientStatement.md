# The topological quotient of the actual complex parameter space

`RationalComplexParameterQuotientStatement` is a proposition specifying the
quotient topology of the complex exponential in Renard 2026 V.3.20. This
file supplies a statement, not its proof. It uses the existing actual
valuation image, period subgroup and pointwise parameter topology.

The registered source is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026,
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant passage is V.3.19–V.3.20, printed pp.115–116/PDF pp.121–122:
the finite-rank actual valuation image, its complex additive dual, the
surjective exponential with integer-dual periods, and the resulting
complex torus. The explicit open-map assertion and commuting quotient
homeomorphisms are derived topological formulations of that passage;
they are not separately numbered source theorems.

Put `Lambda = Additive (rationalDiscreteValuationImage G)`,
`V = Hom_Z(Lambda, C)` and `L = log q`, where `q` is the actual residue
cardinality. The reused exponential is
`E(lambda)(a) = exp(-lambda(a) * L)`. Its stated period subgroup is the
actual range `P = (2*pi*i/L) Hom_Z(Lambda,Z)`. The domain carries
`rationalImageComplexParameterTopology G`, the topology of pointwise
convergence on these additive functionals. The published finite-coordinate
continuous linear equivalence identifies this topology with the usual
finite-dimensional complex vector topology for a connected reductive group.
The group quotient `V/P` carries the quotient topology from that domain;
its subgroup is not replaced by the full real or complex integer dual.

The target retains all field, valuation, topology, nonarchimedean-local-field,
and connected-reductive quantifiers. Affineness and smoothness are derived
from connected reductivity. No splitting, characteristic-zero, finite-rank
or special linear-group premise is added. The finite actual-image basis
is supplied by the shared rational-character lattice theorem.

The four conclusions are:

1. The actual-image exponential is an open quotient map: it is surjective,
   continuous and open into the existing compact-open character topology.
2. There exists a homeomorphism from `V/P` to those actual-image characters
   whose composite with the quotient projection is exactly `E`.
3. The exponential onto actual continuous unramified characters of `G(F)`
   is also an open quotient map, with the additive parameter topology.
4. There exists a homeomorphism from the same quotient to those actual-point
   characters whose composite with the projection is their canonical
   exponential.

The prescribed formulas determine both homeomorphisms uniquely because the
quotient projection is surjective. They specify the quotient induced by
the existing exponential, rather than an unrelated homeomorphism between
the carriers. In the actual-point assertions the point group carries
`rationalPointTopology F G.X`, and the character group has its existing
subgroup topology in the compact-open space of continuous characters.
The existing canonical image-to-unramified equivalence relates the two
character targets.

A proof can express the exponential in the published finite coordinates
as the product of `z ↦ exp(-z*L)` into complex units. Each scalar map is
surjective, continuous and open; the coordinate homeomorphisms transport
those properties. The exact period-difference criterion of
`RationalComplexParameterStatement` then identifies its fibers with the
cosets of `P`, giving the commuting quotient homeomorphisms. This route is
an intended proof plan only; this statement does not assume that algebraic
proposition or any of its conclusions as a premise.

This unit does not assert discreteness or cocompactness of the periods,
the compact imaginary quotient, algebraic torus representability or its
algebraic structure, the character tensor-space or split-center comparisons,
or the pure-tensor norm formula. These remain separate construction and
proof obligations. It preserves the normalization correction recorded by
`RationalComplexParameterStatement`: the lift's real part is
`-log norm/log q`, and the raw logarithmic modulus is `-log q` times it.
