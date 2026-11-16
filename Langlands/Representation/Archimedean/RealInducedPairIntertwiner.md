# Intertwining of the four-crossing induced-pair map

Worker 765 derives this supporting result from the concrete position exponents,
the four-crossing map of `RealInducedPairFrobenius`, the proved intertwining
criterion for `blockFrobMap`, and the proved composition calculus in
`RealStandardFiltration`. No external literature or classification result is
used.

For arbitrary complex character data `d,e`, write
`L = d.weight.natAbs`, `M = e.weight.natAbs`, and set
`delta = d.exponent - L/2 - e.exponent - M/2 + 1`.
This is `swapParameter d e`. Suppose four integer-indexed complex sequences
satisfy `MultiplierData d e delta mu1 mu0 mu2 mu3`, with precisely the
recurrence and symmetry conditions specified by that structure.

`RealInducedPairIntertwinerStatement` says that the already constructed map
`h.swap` from the actual `O(4)`-finite standard module of `[induced d,induced e]`
to that of `[induced e,induced d]` satisfies `IsRealIntertwinerModulo` modulo
the zero submodule. Thus it commutes with right translation by every element
of `O(4)` and with every real matrix right derivative. The theorem
`realInducedPairIntertwiner` proves this statement. The stronger helper
`swap_isRealIntertwinerModulo` gives the same conclusion modulo any supplied
target submodule, since its differences are zero.

The implemented proof first checks the four actual position-exponent
differences plus one. For the word of crossing positions `1,0,2,1`, these are
respectively `delta`, `delta+L`, `delta+M`, and `delta+L+M`. Expanding the
actual split-character definitions reduces each equality to polynomial
arithmetic over the complex numbers. Each corresponding recurrence therefore
discharges `isRealIntertwinerModulo_blockFrobMap`.

The public helper `RealInducedPairFrobenius.inclusion_intertwiner` shows
that the inclusion from the original two-block standard module into its
full-character principal series is also an exact intertwiner: its underlying
function is unchanged, and standard-module stability gives the translated
and differentiated functions in its source. Repeated `modulo_comp_bot`
then proves exact intertwining for the full-character composite `to4`.
Finally `swap` is its codomain restriction to the already proved landing
submodule. Equality of the underlying functions transfers both exact
identities to that codomain.

The result imposes no nonzero-weight or exponent-order assumption. It retains
the four multiplier recurrence and symmetry conditions and does not establish
their existence, nonvanishing, injectivity, surjectivity, linked-parameter
kernel structure, or `RealInducedInducedFiltrationStatement`.
