# Local occurrence from compact adelic convolutions

An isometric adelic action with continuous orbits and compact integrated operators on
compactly supported continuous weights has an irreducible admissible local occurrence
in every nonzero complete invariant subspace. The place is finite, and the occurrence
intertwines the original right action with the action of the local group inserted at
that place.

The proof works on the complete invariant subspace. Van Dantzig's theorem and Haar
averaging give a nonzero compact-open fixed vector. The symmetric approximate identity
for the away action has some operator that acts nontrivially on this vector. The Haar
inversion density writes this operator as a left-Haar integrated action for a
compactly supported continuous weight. It commutes with the local group by
`awayAction_commute`.

For any compact open local subgroup, form the product of its indicator with the
chosen away weight under `placeSplitting`. By `compression_split_eq`, compressing the
integrated action of this product to the invariant subspace gives the local averaging
operator composed with the away operator. On the fixed space the local averaging
operator acts by the nonzero Haar mass of the subgroup. This proves the compactness
on fixed spaces needed by `exists_irreducible_of_compactOnFixedSpaces`. Composing the
resulting injective intertwiner with the original subspace inclusion gives the occurrence.

The argument combines the published split integration formula with the compact
self-adjoint eigenvalue method. The compactness premise is the operator input in
`GroupSchemeFullAEL2CuspidalDecompositionStatement`. In the cuspidal application it is
supplied by the compactness consequence of Getz–Hahn, Theorem 9.1.2, for which the
Library statement documents the source comparison.
