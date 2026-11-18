# The rank-zero real standard module

This internal edge-case module supports Task 7158. It states and proves
`RealRankZeroStandardIrreducibleStatement`: for every list of real blocks of total
rank zero, the actual standard module's compact-finite part, with
`realStandardRep` and `realStandardLie`, is irreducible. The equal-exponent
hypothesis is unnecessary in rank zero.

Each real block has rank one or two, so such a list is empty. The group
`GL₀(ℝ)` is a singleton. The principal-series transformation character is an
empty product and hence one, and the empty list imposes no block Fourier
conditions. Every constant function is therefore smooth and belongs to the
empty standard module. Evaluation at the identity injects the whole function
space into `ℂ`; this also gives finite-dimensionality, so the constants are
compact-finite.

The implemented map `evalEquiv` is a complex linear equivalence between this
compact-finite function space and `ℂ`, with inverse the constant functions.
It proves nontriviality. Every nonzero subspace contains a nonzero function
`f`; every function `g` is the scalar multiple `g(1)/f(1)` of `f`, so the
subspace is the whole space. This proves irreducibility for the actual compact
and Lie actions without requiring further information about those actions.

The module is an internal derivation from the Library's definitions. It uses
no positive-form, R-group, Langlands quotient or classification result and does
not address the positive-rank analytic obligations.
