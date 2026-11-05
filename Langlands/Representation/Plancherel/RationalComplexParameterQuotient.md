# The quotient topology of actual complex exponential parameters

Authors: Worker 6 (original proof), Worker 1444 (verification and submission).

`rationalComplexParameterQuotient` proves the exact published proposition
`RationalComplexParameterQuotientStatement`. Its four conclusions give open
quotient maps and the prescribed homeomorphisms from the actual period
quotient, first to actual-image characters and then to actual continuous
unramified characters of the rational-point group. The independently published
algebraic proof module `RationalComplexParameter` supplies the exact period
fibers. Its theorems are imported by Lean name, without adding the algebraic
proposition as a premise.

The provenance is the derived topological formulation of David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, V.3.19–V.3.20, printed pp.115–116/PDF pp.121–122, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source identifies the actual valuation image, its complex additive dual,
the exponential and its integer-dual periods. The explicit openness and
commuting homeomorphisms are derived conclusions, not separately numbered
source assertions. The implemented proof follows the finite-coordinate
topological route documented by the statement.

Put `Lambda = Additive (rationalDiscreteValuationImage G)`,
`V = Hom_Z(Lambda,C)`, `L = log q` and
`P = (2*pi*i/L) Hom_Z(Lambda,Z)`. Throughout, `V` has the published
pointwise topology, `V/P` has its group quotient topology, and the character
spaces have their existing compact-open topologies. The exponential is
`E(lambda)(a) = exp(-lambda(a)*L)`.

The scalar argument regards complex exponentiation as a surjective,
continuous, open map to the nonzero complex subtype. Surjectivity uses
`Complex.exp_log`, continuity uses `Complex.continuous_exp`, and openness
uses `Complex.isOpenMap_exp` and the open embedding of the nonzero subtype.
The canonical homeomorphism with complex units and the invertible scaling
`z ↦ -z*L` give the scalar open quotient map. The scaling is invertible
because the residue cardinality is greater than one and hence `L ≠ 0`.

`rationalImageComplexCharacter_isOpenQuotientMap` uses the published
continuous linear coordinates on `V` and multiplicative homeomorphism
coordinates on actual-image characters. Both evaluate the same actual
integer basis. In those coordinates `E` is definitionally the product of
the scalar maps. Mathlib's `IsOpenQuotientMap.piMap` and composition with
the two coordinate homeomorphisms prove surjectivity, continuity and
openness of `E`.

`rationalImageComplexParameterQuotient_exists` descends `E` by
`Quotient.lift`. The imported exact algebraic criterion
`E(lambda) = E(mu) ↔ lambda - mu ∈ P` proves that this descent is
well-defined and injective; algebraic surjectivity proves its
surjectivity. The standard quotient projection is a quotient map, so
continuity of `E` gives continuity of the descended equivalence.
Openness descends along the continuous surjective quotient projection.
`Equiv.toHomeomorphOfContinuousOpen` then yields a homeomorphism whose
value on every projected parameter is exactly `E(lambda)`.

The final theorem derives affineness and smoothness from connected
reductivity and installs the canonical rational-point topology. Composing
the first open quotient map and quotient homeomorphism with the existing
canonical image-to-unramified multiplicative homeomorphism gives the last
two clauses. Their commutation formula is the definition of the canonical
complex exponential together with the first quotient commutation formula.

No finite-rank, splitting, characteristic-zero or special linear-group
hypothesis is added. The shared rational-character lattice theorem
supplies the finite actual-image coordinates. This proof retains the
`q^(-s)` convention and actual period subgroup. It also preserves the
normalization correction in the statement: the real part of a lift is
`-log norm/log q`, and the raw logarithmic modulus is `-log q` times that
functional. Discreteness or
cocompactness of periods, the compact imaginary quotient, character tensor
and split-center comparisons, the pure-tensor norm formula and algebraic
torus structure remain separate obligations.
