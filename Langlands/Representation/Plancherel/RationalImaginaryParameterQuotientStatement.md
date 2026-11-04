# Actual periods and the compact imaginary parameter quotient

`RationalImaginaryParameterQuotientStatement` specifies the discreteness
of the original periods and the compact imaginary quotient in Renard
2026 V.3.20, printed p.116/PDF p.122. This file supplies a proposition,
not a proof. Worker 6 authored this statement.

The registered source is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026,
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The passage identifies the exponential kernel with a scaled integer dual,
calls it a lattice, and identifies the unitary characters with the compact
quotient of the imaginary parameter space by that lattice. Closedness,
explicit open quotient maps and their commuting homeomorphisms are
derived topological formulations of that passage, rather than separately
numbered source assertions.

Write `Lambda = Additive (rationalDiscreteValuationImage G)`,
`V = Hom_Z(Lambda,C)`, `L = log q`, and
`P = (2*pi*i/L) Hom_Z(Lambda,Z)`. All these are the existing actual
valuation-image constructions. The imaginary group `I` is the actual
subgroup of functionals in `V` whose values have zero real part.
The restricted period subgroup `P_I` is the inverse image of `P` under
the inclusion `I -> V`; the construction's exact image equality shows
that it consists of the same original periods.

The topology on `V` is `rationalImageComplexParameterTopology G`,
the topology of pointwise convergence. The imaginary group, `P` and
`P_I` have the inherited subgroup topologies. The quotient `I/P_I`
has the standard additive-group quotient topology. The character spaces
retain their existing subgroup topologies in the compact-open spaces of
continuous characters. The actual point group uses the canonical
`rationalPointTopology F G.X`.

The proposition asserts nine conclusions:

1. The original subgroup `P`, inside the complex parameter space, has
   discrete topology.
2. It is closed in that complex space.
3. The same periods `P_I`, inside the imaginary parameter group, have
   discrete topology.
4. They are closed in the imaginary group.
5. The actual quotient `I/P_I` is compact.
6. The restricted exponential from `I` onto the actual-image unitary
   characters is surjective, continuous and open.
7. It induces a homeomorphism from `I/P_I` to those unitary characters,
   with value `E(lambda)` on every projected parameter.
8. The canonical restricted exponential onto actual continuous unitary
   unramified characters of `G(F)` is also an open quotient map.
9. It induces a homeomorphism from the same quotient to those actual-point
   characters, again with the prescribed value on every projected parameter.

Both exponentials use the existing formula
`E(lambda)(a) = exp(-lambda(a)*L)`. Their prescribed values determine the
homeomorphisms uniquely because the quotient projection is surjective.
Thus the conclusion identifies the quotient induced by this exponential.
Compactness is asserted for the imaginary quotient. Discreteness and
closedness of the periods are also asserted in the full complex space.

All field, valuation, topology, nonarchimedean-local-field and
connected-reductive quantifiers are retained. Affineness and smoothness
are derived from connected reductivity. The finite actual-image basis
is supplied by the shared rational-character lattice theorem. There is
no additional finite-rank, splitting, characteristic-zero or special
linear-group premise, and no desired quotient property is assumed.

One possible proof route uses the published actual-image basis to put
the periods into a finite product of scaled integer subgroups of `C`,
which proves discreteness and closedness. The unitary-character
preimage theorem identifies the imaginary group with the preimage of
the unitary subgroup under the complex exponential. Restricting the
complex open quotient map to this preimage gives an open quotient map;
its exact period fibers give the commuting homeomorphism. Compactness follows
from the existing compactness of the actual-image unitary character
group. The canonical unitary character homeomorphism transports the
last two assertions to actual rational points. This paragraph is a proof
plan, not accepted proof evidence.

Algebraic torus representability and algebraic structure, the smooth
real submanifold assertion, the character tensor-space and split-center
comparisons, and the pure-tensor norm formula remain separate
obligations. The normalization correction of the existing complex
parameter statement is preserved: the lift's real part is
`-log norm/log q`, and its raw logarithmic modulus is `-log q` times it.
