# Exact pinned representatives from supplied pinned full faithfulness

This internal conversion uses
`AffinePinnedIsomorphismTheoremStatement` as an explicit hypothesis. It does
not prove that statement or assert unconditional existence of representatives.

For an `AffinePinnedModel M` and a label `θ` preserving the chosen base,
`existsUnique_pinnedAutomorphism` gives exactly one automorphism satisfying
`M.IsPinnedAutomorphism σ θ`, conditional on the supplied full-faithfulness
statement. The character convention in that predicate is covariant, whereas
the isomorphism theorem is stated using pullback. The proof therefore applies
the theorem to the two identical models with root-datum equivalence `θ⁻¹`.
Substituting `θ.weightMap m` in its character identity gives the target
identity. Reindexing the simple vectors by `θ.indexEquiv` gives the required
pinning formula. For uniqueness, the substitutions are reversed to place any
other exact pinned automorphism under the theorem's uniqueness clause.

`pinnedAutomorphismHom` chooses these unique representatives and is a group
homomorphism from `M.basedAutomorphisms` to the actual automorphisms of
`M.group`. Its identity and product laws follow from uniqueness and the
identity and product laws of the exact pinned predicate.
`pinnedAutomorphismHom_pinned` and `eq_pinnedAutomorphismHom` identify the
chosen value with every exact pinned representative.

This is a derived change of conventions between two published statement
interfaces. It does not require a connected base. Geometric factorization
and separation remain separate obligations for the automorphism-group
theorem.
