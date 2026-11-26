# Split types in matrix coordinates

For \(G=\mathrm{GL}_n(F)\) and \(V=F^n\), `glSubgroupToAut` sends a
matrix subgroup to its image under `Matrix.GeneralLinearGroup.toLin`.
`glRepresentationToAut` transports its smooth representation along
the inverse of the restricted group equivalence. The four split-type
predicates on \(\operatorname{Aut}_F(V)\) apply to this transported pair.

The predicates use the same additive character \(\psi_F\) as
`IsGLSimpleType`. Each case involving a positive first level requires
`IsBKAdditiveCharacter ψF`. The \((0,0)\) case uses the residue-field
representations alone.

`IsGLPositiveLevelSplitType` covers levels \((x,x)\) for \(x>0\) and
\((x,y)\) for \(x>y>0\). `IsGLZeroSecondLevelSplitType` covers levels
\((0,0)\) and \((x,0)\) for \(x>0\). `IsGLSplitType` holds when either
predicate holds.

The subgroup of a split type is compact and open. For \(H^m\), the
recursion defining the simple-stratum lattice \(\mathfrak H\) contains
a sufficiently deep filtration lattice. Thus \(H^m\) contains some
\(U^k(\mathfrak A)\) and is contained in \(U(\mathfrak A)\).
These inclusions give openness and compactness using
`SimpleTypeTopology`. The same module supplies compact openness for
the unit group and \(J\). The homeomorphism `generalLinearToLinContinuous`
gives the conclusion for the matrix subgroup.

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via
compact open subgroups* (1993), (8.1.1)–(8.1.4), printed pp. 266–267,
and (3.1.7)–(3.1.8), (3.1.14), printed pp. 90–91, 95, for the
simple-stratum lattices and groups. The conductor convention is in
the setup to §8.1, printed p. 266.
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`.
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
