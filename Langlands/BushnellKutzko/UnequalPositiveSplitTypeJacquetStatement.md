# Jacquet nonvanishing for a split type of level \((x,y)\) with \(x>y>0\)

`UnequalPositiveSplitTypeJacquetStatement` is the case \(x>y\) of
`PositiveLevelSplitTypeJacquetStatement`. It says that an irreducible
admissible smooth complex representation \(\pi\) of \(\mathrm{GL}_n(F)\)
containing a split type of level \((x,y)\) with \(x>y>0\) has a nonzero
Jacquet module for some proper parabolic subgroup. The split type is
given by `IsUnequalPositiveSplitType` after transport along
`glRepresentationToAut`, so the pair is
\((H^m(\beta,\mathfrak A),\theta\psi_c)\) of BK93 (8.1.3), and
containment is `ContainsType`.

The quantifiers and the conclusion are those of
`PositiveLevelSplitTypeJacquetStatement`. The statement ranges over
every nonarchimedean local field \(F\), every \(n>0\) and every additive
character \(\psi_F\) satisfying `IsBKAdditiveCharacter`, with
independent universes for the field and the two representation
carriers. The conclusion chooses a `BlockShape` \(B\) whose parabolic is
proper and a matrix \(g\) such that the coinvariants of \(\pi\) by
`B.conjugateUnipotent g` are nonzero, expressed by `¬ Subsingleton`.

In the source, the theorem (8.2.5) attaches to a split type of level
\((x,y)\), \(x>y>0\), a decomposition \(V=V_1\oplus V_2\) into proper
\(E\)-subspaces splitting the stratum \([\mathfrak B,m,m-1,s(c)]\). Part
(iv) shows that the Jacquet modules of \(\pi\) for both parabolic
subgroups attached to this decomposition are nonzero. They contain
the restriction of \(\theta\psi_c\) to \(K\cap M\), where \(M\) is the
common Levi subgroup. The Lean statement records only nonvanishing for
some proper standard block parabolic up to conjugation. It takes
admissibility explicitly.

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via
compact open subgroups* (1993), (8.2.5)(iv), printed pp. 276–277. The
setup is on p. 275 and the proof of this case runs through p. 289.
The split type is (8.1.3), printed p. 267.
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`.
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
