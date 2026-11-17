# The three-block rectangular chart and integral trailing roots

This internal coordinate module connects the preceding local minor bounds to
the three-block matrix used by the rectangular adelic integral.
`extendRectangle c x` appends `c` zero rows to `x`. Reindexing
`lowerBlockLocalization c g x 1` by the associativity equivalence
`Fin ((a+d)+c) ≃ Fin (a+(d+c))` gives exactly
`lowerBlockPair g (extendRectangle c x) 1`. The implemented proof checks
the nine blocks using the published coordinate formulas. Every row of
the final identity block is a standard basis row in the full matrix.

The subring lemmas use elementary multiplicative algebra. If the last
entry of a unit diagonal tuple lies in a subring and all adjacent ratios
lie there, every entry lies there. Lean proves this by reverse induction,
multiplying each adjacent ratio by the following diagonal entry.
For a factorization `G=B*K`, a standard basis row of `G` identifies
the corresponding diagonal entry of `B` with the same entry of `K⁻¹`.
This follows by multiplying the factorization by `K⁻¹` and expanding
that matrix entry. Consequently integral entries of `K⁻¹` make this
diagonal entry integral.

The final valuation-ring theorem combines these facts for the chart
with one final identity row. It assumes a factorization of the
reassociated chart as `B*K`, with `B` upper triangular and both `K` and
`K⁻¹` integral. If the adjacent ratios among the final `d+1` diagonal
entries of `B` are integral, then every entry of `x` is integral.
The proof uses the final standard basis row to make the last diagonal
entry integral, reverse induction to make the entire trailing diagonal
integral, and `lowerBlockPair_coordinate_mem_integer` to recover the
rectangle. This gives the local constant-one support implication under
explicit hypotheses; it does not assume a local-field model or a
residue-cardinality normalization.

The module asserts algebraic identities under explicit factorization
hypotheses. It does not yet establish the global Schwartz majorant,
adelic finite support, or the target Mellin convergence.
