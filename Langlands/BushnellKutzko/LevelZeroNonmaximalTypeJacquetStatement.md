# Jacquet modules of representations containing a non-maximal level-zero simple type

`Langlands.BushnellKutzko.LevelZeroNonmaximalTypeJacquetStatement` applies to
every nonarchimedean local field \(F\) and every \(n>0\). Let \(J\) be a subgroup
of \(\mathrm{GL}_n(F)\) and \(\rho\) a smooth complex representation of \(J\).
The hypothesis `IsLevelZeroSimpleTypeData L e (glRepresentationToAut ρ)`
exhibits \((J,\rho)\) as a simple type of kind (b), with lattice chain \(L\)
in \(F^n\) and period \(e=e(\mathfrak A\mid\mathfrak o_F)\). Assume \(e\ge 2\).

For every smooth complex representation \(\pi\) with `ContainsType π ρ`,
there are a block shape `B : GeneralLinear.BlockShape n` with
`B.parabolic F ≠ ⊤` and an element \(g\in\mathrm{GL}_n(F)\) such that
`Jacquet.Coinvariants π.representation (B.conjugateUnipotent g)` has a nonzero
element. Lean expresses this as `¬ Subsingleton` of the coinvariant quotient.
The subgroup is the conjugate by \(g\) of the unipotent radical of the proper
standard upper block parabolic, as in `GeneralLinear.IsSupercuspidal`.
The field and the carriers of \(\rho\) and \(\pi\) have independent universes.

In kind (b), Bushnell and Kutzko specialize to \(E=F\) and
\(\mathfrak B=\mathfrak A\). The first remark after (7.3.2) identifies the
subordinate parabolic as proper when the period \(e\) is at least two.
For that parabolic, inflation from the residue quotient makes the type
trivial on \(J\cap U\), where \(U\) is the unipotent radical. Containment of the
type therefore gives a nonzero vector in the auxiliary \(\lambda_P\)-isotypic
space. By (7.3.6)(i), the injectivity part of (7.3.2) applies to this space
for every smooth \(\pi\), so a nonzero vector survives in the Jacquet
quotient.

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via compact open
subgroups* (1993), (5.5.10)(b), printed p. 185 (PDF p. 197),
(7.3.2) and its first remark, printed p. 223 (PDF p. 235), and
(7.3.6)(i), printed p. 225 (PDF p. 237).
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`.
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
