# Reduction of positive-level Jacquet nonvanishing to the case \(x>y\)

`PositiveLevelSplitTypeJacquetReductionStatement` is the implication
from `UnequalPositiveSplitTypeJacquetStatement` to
`PositiveLevelSplitTypeJacquetStatement`, with the same universes
\(u_F,u_\pi,u_\rho\) on both sides. The theorem
`positiveLevelSplitTypeJacquet_of_unequal` proves it.

A positive-level split type in matrix coordinates
(`IsGLPositiveLevelSplitType`) has level \((x,x)\) with \(x>0\) or
level \((x,y)\) with \(x>y>0\).

- Level \((x,x)\): the subgroup of a split type is compact and open
  (`IsGLSplitType.isCompact_isOpen`).
  `SplitBlocks.diagonalSplitType_jacquet_nonvanishing`
  (`DiagonalSplitTypeJacquet`) then gives the nonzero Jacquet module.
  This case uses admissibility and containment, not irreducibility.
- Level \((x,y)\), \(x>y>0\): this is the premise, applied to the same
  data.

Both cases are part of Bushnell–Kutzko (8.2.5)(iv); the source treats
the case \(x=y\) together with \(x>y\) by putting \(E=F\),
\(\mathfrak B=\mathfrak A\), \(n=m\) and \(s=\mathrm{id}\) (printed
p. 275).

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via
compact open subgroups* (1993), (8.2.5)(iv), printed pp. 275–277.
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`.
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
