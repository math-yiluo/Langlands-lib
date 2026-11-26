# Simple types in matrix coordinates

For \(G=\mathrm{GL}_n(F)\) and \(V=F^n\), `glSubgroupToAut` sends a subgroup
\(J\) to its image under `Matrix.GeneralLinearGroup.toLin`. The
representation `glRepresentationToAut` is obtained by precomposing with
the inverse of that equivalence restricted to \(J\). The original pair
is recovered along `toLin⁻¹`. `IsGLSimpleType` and `IsGLMaximalSimpleType`
apply the predicates in `SimpleTypes` to this pair. The source setting is
smooth complex representations over a nonarchimedean local field.

`GLSimpleTypeData` retains the data exhibiting a pair of either kind.
For kind (a) it retains the simple stratum, the defining-sequence choice
and the period \(e(\mathfrak B_\beta\mid\mathfrak o_E)\) of the centralizer
order. The simple stratum gives the field structure on the generated
subalgebra \(E=F[\beta]\). For kind (b) it retains the lattice chain and
its period \(e(\mathfrak A\mid\mathfrak o_F)\), with \(\beta=0\) and \(E=F\)
acting by scalars. `ramificationIndex` uses `subfieldRamificationIndex` on
this field in both cases. Maximality of the matrix pair is equivalent
to the existence of data of period one.

For either kind, the subgroup of the transported pair is compact open.
In kind (a) the data identify its image with `simpleJ`, and in kind (b)
with the unit group of the lattice-chain order. The homeomorphism in
`SimpleTypeTopology` carries these compact open subgroups back to the
matrix group with the topology of `GeneralLinear`.

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact
open subgroups* (1993), (5.5.10), printed pp. 184–185, the identification
of the two general linear groups on printed p. 199, and the definition of
maximality immediately before (6.2.3), printed p. 204.
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`.
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
