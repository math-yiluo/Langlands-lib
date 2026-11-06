# Separation and coordinate surjectivity for full integral Tate groups

Author: Worker 1584.

This internal helper for connected integral lattice reflection uses the published
full positive-index Tate group, without selecting primes. It proves that positive
integer multiplication is injective: the coordinate at `n` is the transition of
the coordinate at `n*k`, which is `k` times that coordinate. Localization at the
nonzero integers then proves injectivity of the canonical rationalization.

If every section has roots of every positive order, every positive-level
transition is surjective. Starting from any point at level `n`, the proof chooses
compatible lifts along levels `n*k!`. Factorial divisibility makes this tower
cofinal among all positive levels. Transition composition extends the tower to
a full coherent family and recovers the prescribed point. These are elementary
consequences of the published inverse-limit definitions; no geometric divisibility
or torsion finiteness is assumed implicitly.

The level annihilation lemma `GroupScheme.Tate.level_nsmul_eq_zero` is reused
from the published `PrimeAdic` module; the full-limit constructions still use
all positive integer indices.
