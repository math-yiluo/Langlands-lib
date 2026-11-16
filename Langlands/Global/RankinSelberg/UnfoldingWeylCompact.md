# The unfolding Weyl representative lies in the standard compact subgroup

This is internal matrix and adelic infrastructure for the rectangular
Whittaker gauge bound. The argument uses the published definitions of
`unfoldingWeyl` and `PrimitiveAdelicHeight.standardCompact`; it introduces no
analytic convergence assumption.

For every number field `F : Type u`, every `t < r`, the actual adelic Weyl
representative `unfoldingWeyl F h = diag(I_(t+1), w_(r-t))` lies in the standard
compact subgroup: it is orthogonal at real places, unitary at complex places,
and invertible with integral entries at every finite place.

The proof first identifies block sums and reindexings of permutation matrices
with their corresponding permutations. `unfoldingWeylPermutation h` fixes the
first block and reverses the complementary block, and
`unfoldingWeyl_eq_permutation` identifies its matrix with the Library's Weyl
representative. Every permutation matrix lies in the standard compact:
its conjugate transpose is its inverse at each infinite place, and both
it and its inverse have entries zero or one at each finite place.
`unfoldingWeyl_mem_standardCompact` applies this general fact.

The conclusion is independent of additive characters, cuspidal realizations,
and compactness of the additive adelic quotient. It is used to remove the
right Weyl translation from a standard-compact-invariant simple-root gauge.
