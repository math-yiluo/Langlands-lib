# Operator trace: implemented laws

Worker 116 proves `OperatorTraceLawsStatement` for the actual chosen-basis
function `operatorTrace`. The space, second space and supplied-basis index
universes are independent. The aggregate consists exactly of the supplied-basis
formula with absolute convergence, complex linearity on trace-class operands,
and bounded rectangular cyclicity including trace-class membership of both
endomorphisms.

`operatorTraceBasis` applies the published `traceBasisIndependence` theorem to
the basis selected in `operatorTrace` and the supplied basis. Its conclusions
give absolute norm summability in the supplied basis and the required equality.
The selected basis depends only on the space and its structures.

`operatorTrace_zero` simplifies every diagonal term to zero. For
`operatorTrace_add` and `operatorTrace_smul`, the basis theorem supplies absolute
summability of the operands' diagonals in that same selected basis. Summability
of the complex diagonals follows from summability of their norms. Termwise
second-argument linearity of Mathlib's inner product and the summable addition
and multiplication rules for `tsum` give the claimed formulas. The complex
scalar is unchanged, without conjugation. `operatorTraceLinearity` collects
these three formulas.

For `operatorTraceCyclicity`, let A:E→E be trace class, with arbitrary bounded
complex-linear B:E→F and C:F→E. The published trace-class sandwich and
precomposition laws first prove that B A C and A C B are trace class. Choose
Hilbert bases b of E and d of F, and identify both operator traces with their
supplied-basis sums. The published factorization gives A=U V with U,V
Hilbert–Schmidt. The Hilbert–Schmidt ideal laws make B U, V C and V C B
Hilbert–Schmidt. Apply the product-diagonal theorem first to V C:F→E and
B U:E→F, comparing the d-trace of B U V C to the b-trace of V C B U. Apply
it again to V C B:E→E and U:E→E, comparing the b-trace of U V C B with
the same b-trace of V C B U. Composition associativity and the factorization
identify the two requested endomorphisms, and equality through the common
sum completes the proof. No trace property is assumed in the factorization
or ideal predicates.

This is an internal derivation from published Library operator results, rather
than a new theorem attributed verbatim to Getz–Hahn. The unchanged target's
Markdown records its motivating original passages, conventions and complete
errata check. This proof retains the positive left modulus `sqrt(A A*)`,
arbitrary complete complex inner-product spaces and independent basis indices.
It requires neither separability nor finite dimensionality. It proves no trace
laws outside the trace-class domain, trace-norm estimate, automorphic operator
existence, kernel formula or spectral theorem.
