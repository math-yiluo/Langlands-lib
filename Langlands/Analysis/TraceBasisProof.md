# Proof of complex trace basis independence

`Langlands.Analysis.OperatorIdeals.traceBasisIndependence` proves
the full `TraceBasisIndependenceStatement`, with absolute summability
and independent arbitrary universe parameters for the space and the
two Hilbert-basis index types.

Factor the actual trace-class endomorphism as A = B C with both factors
Hilbert–Schmidt, using `traceClassFactorization`. Apply
`hilbertSchmidtProductTrace` to C and B with b as both supplied bases.
It gives absolute summability of A's diagonal in b and equality between
its sum and the diagonal sum of C B in b. Apply the same theorem with
c as the first basis and b as the second. It gives absolute summability
of A's diagonal in c and equality to that same diagonal sum of C B
in b. Transitivity proves the required equality for A.

The statement Markdown records the source trace convention and the
extension beyond separable spaces. The proof uses the two explicit
operator prerequisites above; neither trace basis independence nor
trace-class membership of arbitrary Hilbert–Schmidt products is assumed.
No canonical trace function or automorphic operator is constructed here.
