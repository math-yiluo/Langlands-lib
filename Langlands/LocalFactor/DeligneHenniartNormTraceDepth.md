# Norm and trace at a prescribed depth

Worker 126 authored this internal conversion between ideal bounds and the
trace and unit formulation needed for DH81 Corollary 3.12(i).

`NormTraceAtDepth K L TK TL r n` is a proposition for a finite extension of
p-adic fields in independent universes, arbitrary topological data, a real
input depth `r` and a natural output depth `n`. It asserts that every
nonzero element of `L` of order at least `r` has trace in the depth `n`
additive lattice of `K`. For every unit representing `1+y` and every unit
representing `1+Tr(y)`, the quotient of the norm of the first by the second
belongs to the principal units of level `n+1`.

`normTraceAtDepth_of_remainder` proves this property when `n >= 1`, the trace
has depth `n`, and the additive remainder `N(1+y)-1-Tr(y)` has depth `n+1`.
The trace bound makes `1+Tr(y)` have discrete valuation one. Subtracting
one from the required quotient gives the remainder divided by this unit,
which preserves its valuation bound. Its difference from one has valuation
strictly below one, so the quotient itself has valuation one.

`normTraceAtDepth_of_canonical_ideal_bounds` obtains these additive bounds
from actual integral representatives in maximal-ideal powers of the
canonical realizations. It converts the input order bound into integral
ideal membership, applies the supplied bounds, and converts the two output
representatives back to the supplied additive lattices. Realization
independence of orders and discrete valuations comes from the published
`NYLL.ord_eq_of_algEquiv` and `NYLL.discreteValuation_eq_of_algEquiv`,
applied to the identity equivalence.

`prime_normTrace_atDepth` applies that conversion to
`prime_normTrace_ideal_bounds` for a prime-degree totally ramified Galois
extension with a supplied complete single-break pattern. For `n > t` its
input depth is `t + [L:K] * (n-t)`. It treats all allowed input orders, not
only equality, and arbitrary topological data of both fields.

This is a derived proof from imported arithmetic and valuation results.
It does not prove the arbitrary-subextension
`TopLayerNormTraceStatement`, nor the tower and tame-base-change reductions.
