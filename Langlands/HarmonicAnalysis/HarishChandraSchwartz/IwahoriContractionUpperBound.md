# The unipotent upper index bound

This internal algebraic argument uses the actual ordered intersection
factorization `K = V_K M_K U_K`. If `V_K` and `M_K` lie in a subgroup `J`,
inversion gives `K = U_K M_K V_K`, so the natural embedding of the coset space
of `J` in `U_K` into its coset space in `K` is surjective. Hence their indices
agree. This needs only the supplied factorization, without a factorization of
`J`, global big-cell uniqueness, or a common normal subgroup.

For `J = g K g^-1`, normalization of `M_K` and inverse contraction of `V_K`
put these two intersections in `J`. The conjugate of `U_K` is contained in
`J`; monotonicity in the smaller subgroup bounds `[K : K intersect J]` by
`[U_K : U_K intersect g U_K g^-1]` and proves finiteness when that index is
finite. The index is the Library's actual `doubleCosetIndex`, with its stated
conjugation direction. This is an internal derivation, not a new assertion
attributed to a numbered literature result.
