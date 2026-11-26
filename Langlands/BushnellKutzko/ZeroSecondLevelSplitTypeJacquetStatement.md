# Jacquet nonvanishing for a split type of level \((x,0)\)

`ZeroSecondLevelSplitTypeJacquetStatement` says that an irreducible
admissible smooth complex representation \(\pi\) of \(\mathrm{GL}_n(F)\)
containing a split type of level \((x,0)\) with \(x\ge 0\) has a
nonzero Jacquet module for some proper parabolic. It includes both
the level \((0,0)\) construction and the \(\beta\)-extension
construction for \(x>0\). The field \(F\), \(n>0\), and the additive
character \(\psi_F\) satisfying `IsBKAdditiveCharacter` are arbitrary.
The field and the two carriers have independent universes.

The witness is a proper block parabolic and an element of
\(\mathrm{GL}_n(F)\) conjugating its radical. Its `Jacquet.Coinvariants`
on \(\pi\) are nonzero, expressed by `¬ Subsingleton`. In the source,
the proper parabolic is chosen subordinate to the stratum, or to
the order in the case \(x=0\). The source also proves that the Jacquet
module contains the Levi representation \(\vartheta_U\) obtained
from the split type. The Lean conclusion records nonvanishing.
Admissibility is explicit in the Lean hypothesis, as in the
simple-type Jacquet theorem (7.3.2) used in the source proof.

C. J. Bushnell and P. C. Kutzko, *The admissible dual of GL(N) via
compact open subgroups* (1993), (8.3.3), printed p. 291, and
(7.3.2), printed p. 223, for the admissibility hypothesis.
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`.
SHA-256 `811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.
