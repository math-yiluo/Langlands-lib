# Natural coordinates on the quadratic trace-zero line

For a separable quadratic extension `L/k` and a nonzero trace-zero scalar
`η`, `traceZeroBasis` is the actual `k`-basis consisting of the existing
trace-one scalar followed by `η`. Applying the trace proves linear
independence, including in characteristic two.

After arbitrary extension to a commutative `k`-algebra `R`, the basis
decomposition and the actual conjugation equation show that the trace
kernel is precisely the set of tensors `r ⊗ η`. Injectivity of
`R → R ⊗ L` detects the coefficient of the trace-one basis vector.
`tensorTraceZeroEquiv` is the resulting additive equivalence; its
forward map is `r ↦ r ⊗ η`. Its naturality theorem includes arbitrary
coefficient maps and nonreduced algebras.

This is an internal derivation of the all-test coordinate calculation
behind Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Section C.3, printed page 698 (PDF page 729). It does not yet assert an
integral model or identify a supplied relative root subgroup.
