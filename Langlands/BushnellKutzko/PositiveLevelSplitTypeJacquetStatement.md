# Jacquet nonvanishing for a split type of positive level

`PositiveLevelSplitTypeJacquetStatement` says that an irreducible
admissible smooth complex representation \(\pi\) of \(\mathrm{GL}_n(F)\)
containing a split type of level \((x,y)\) with \(x\ge y>0\) has a
nonzero Jacquet module for some proper parabolic. The statement ranges
over every nonarchimedean local field \(F\), \(n>0\), and additive
character \(\psi_F\) satisfying `IsBKAdditiveCharacter`, with
independent universes for the field and the two representation carriers.

The conclusion chooses a `BlockShape` \(B\) with proper parabolic
and a matrix \(g\). The coinvariants of \(\pi\) by
`B.conjugateUnipotent g` are nonzero, expressed by
`¬ Subsingleton`. These radicals are the same ones used by
`GeneralLinear.IsSupercuspidal`. The source uses the two opposite
parabolics attached to a splitting of the stratum. For each of them,
the source also proves that the Jacquet module contains the
restriction of the split-type character to \(K\cap M\), where \(M\)
is the common Levi. The Lean statement records nonvanishing and
takes admissibility explicitly.

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via
compact open subgroups* (1993), (8.2.5)(iv), printed pp. 276–277.
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`.
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
