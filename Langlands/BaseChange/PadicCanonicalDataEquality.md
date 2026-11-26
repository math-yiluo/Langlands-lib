# Equality of supplied and canonical p-adic local-field data

`eq_of_same_padicField` compares two `TopologicalData` structures on the same
algebraic extension of `ℚ_p`. Their topologies are the module topology.
The integer rings are the subrings on which the canonical norm is at most
one. For nonzero `y`, valuation comparison of `x` with `y` is equivalent to
integer membership of `x / y`, and comparison with zero is equivalent to
`x = 0`. Thus the topology and valuative-relation fields agree. The other
fields are proposition-valued.
