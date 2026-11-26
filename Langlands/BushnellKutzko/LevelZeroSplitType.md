# Split types of level \((0,0)\)

`IsLevelZeroSplitType ρ` asks for the lattice chain \(L\) of a hereditary
\(\mathfrak o_F\)-order \(\mathfrak A\), with period \(e\).
`IsPairIsomorphic` identifies the given subgroup with \(U(\mathfrak A)\)
and its representation with an inflation of a tensor product of
irreducible cuspidal representations of the groups
\(\mathrm{GL}_{n_i}(k_F)\). The predicate requires trivial action on
\(U^1(\mathfrak A)\).

`LatticeChain.CuspidalLayerData` chooses a basis of every layer
\(L_i/L_{i+1}\) for \(0\le i<e\) and one irreducible cuspidal factor for
each layer. The basis is indexed by \(\operatorname{Fin}(n_i)\), with
the rank allowed to vary. `LatticeChain.layerReduction` sends each unit
to the matrices of its actions in these bases. The construction uses
`LatticeChain.layerAction` on the quotients and the residue-field scalar
actions, and `layerReduction_spec` gives its effect on the class of a
lattice vector. `CuspidalLayerData.inflation` precomposes the external
tensor product action with this map.

The factors have inequivalent entries if the predicate finds \(i,j\)
with different values of `factorClass`. Each value is a dependent pair
consisting of the rank and the `FiniteGeneralLinear.CuspidalClass` in
that rank. This includes unequal ranks and, at equal rank, inequivalent
representations of the same group. A change of layer basis conjugates
the matrix action within its general linear group, which preserves
representation equivalence.

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via
compact open subgroups* (1993), (8.1.2), printed p. 267, for the split
type and product quotient. The lattice-chain order filtration is
(1.1.2), printed p. 20, and the radical and unit groups are in
§1.1, printed p. 21.
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`.
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
