# Compact induction from a maximal simple type

`MaximalSimpleTypeInductionStatement` quantifies over every nonarchimedean
local field \(F\), positive \(n\), and simple type \((J,\lambda)\) in
\(G=\mathrm{GL}_n(F)\) with exhibited data of period one. The period is
\(e(\mathfrak B_\beta\mid\mathfrak o_E)\) in kind (a) and
\(e(\mathfrak A\mid\mathfrak o_F)\) at level zero, where \(E=F\).
The subgroup \(E^\times J\) is constructed from those same data.

The proposition asserts existence of an irreducible smooth
\(\Lambda\) of \(E^\times J\) whose restriction to \(J\) contains
\(\lambda\). For every such \(\Lambda\), its compact induction satisfies
`GeneralLinear.supercuspidalProperty`, which includes irreducibility,
admissibility and vanishing of the proper Jacquet quotients. Every
irreducible smooth \(\pi\) containing the type is equivalent to such a
compact induction, and equivalence of two induced representations
implies equivalence of their inducing representations.

`GLSimpleTypeData.compactInduce` applies `Induction.smoothCompactInduction`
to `SmoothRep.universeLift` of \(\Lambda\), placing the input carrier in
the function-space universe required by the functor. The field, type,
ambient representation and inducing representations have independent
universe parameters. Equivalence means an actual equivariant linear
equivalence of the underlying representations, using `Representation.Equiv`.

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact
open subgroups* (1993), (6.2.2), printed p. 203, with the existence of
extension and the description of irreducible representations on
restriction in (6.1.2), printed p. 200.
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`.
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
