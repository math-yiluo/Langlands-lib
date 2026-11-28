# Simple strata on chains normalized by the parameter field

`HasDepthZeroStratumChoice D b` asserts that `b` is the parameter of a
depth-zero simple stratum on the lattice chain `D`, with a defining sequence
starting at that stratum and lying on `D`. The depth, parameter and chain
appear directly in the constructor of the stratum.

`exists_depthZeroStratumChoice` proves this predicate for the parameter of a
depth-zero simple stratum when its parameter field normalizes `D`. It applies
`PureApproximation.exists_simple_of_normalized` at depth zero, then uses
`Stratum.exists_exact_definingSequenceChoice` with the pure-stratum
approximation theorem.

This realizes the strata on coarsened and reordered chains used in the change
of order for split types. The chain change uses the critical-exponent formula
of BK93 (1.4.13). The approximation underlying the defining sequence is
BK93 (2.4.1), with the sequence defined in (2.4.2).
Source `bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`,
printed p. 39 and p. 65 (PDF pp. 51 and 77).
