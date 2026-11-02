# The standard-subset dictionary for the actual complex

Internal construction by Worker 194.

The normalized complex uses a removed-root index `s`. A standard parabolic family
uses the surviving subset `J`, with `P(J)` increasing and `U(J)` decreasing.
`removedFamily F s = F(S \ s)` converts these conventions. Its order laws
are proved from reversal of inclusion by complement.

The wrappers `degreeObject`, `differential`, `sharpObject`, `sharpFunctor`,
`boundary`, `terminalProjection`, `initialMap`, `initialEquiv` and
`initialDifferential` apply the actual constructions to this
complementary family. `termObject_eq` verifies that the coordinate at `s` is the
genuine normalized `i_(S \ s) r_(S \ s)` object. The original support subset `I`
is passed unchanged to `sharpObject`; it selects removed-root degree
`|S| - |I|`. `terminalIndexEquiv I` proves by complementation that its
coordinates correspond exactly to surviving subsets `J` of cardinality `|I|`.
The original exterior signs and canonical quotient maps are retained by these
wrappers. The endpoint requirements for the initial equivalence are
`P(S) = G` and `U(S) = 1`, including the case of an empty root set.

These constructions take actual subgroup families with explicit semidirect,
closedness, unimodularity and nesting hypotheses. They do not construct the
standard-subset realization of a connected reductive group or prove its
structural properties. Unimodularity remains an in-book proof obligation in the
general application. No exactness, support, finite-length or irreducibility
consequence is asserted by this internal dictionary.
