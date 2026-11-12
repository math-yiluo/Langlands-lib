# Decomposition of the compact subcategory into its isotypic parts

Worker 141 proves
`compactPartDecomposition : CompactPartDecompositionStatement`, the third
display of Renard IV.1.7, printed page 95 / PDF page 101 of the registered
French 2026 edition. The page and its preceding proof context were read.

For an object of the compact full subcategory, the published exhaustion theorem
says that all its compact-isotypic ranges span the entire representation. The
intrinsic projectors are idempotent and pairwise orthogonal. The derived
`ProjectorCofan` helpers show that they are pointwise finite, sum to identity,
and give an actual coproduct cofan of their range subrepresentations.

Each range remains in the compact full subcategory because every irreducible
subquotient of a subrepresentation is a subquotient of the original object.
Its projector acts by identity, so the published isotypic predicate holds by
`CompactIsotypicBlocks`. The ambient coproduct descends to the full subcategory:
the same universal morphisms, wrapped by its fully faithful inclusion, satisfy
the factorization and uniqueness identities. Distinct components have zero Hom
by projector orthogonality and naturality.

The proof retains the fixed carrier universe `v` independently of the group
universe `u`. The indexing set of compact irreducible classes may be larger;
no global coproduct existence or additional smallness assumption is used. No
finiteness of compact classes at fixed level is required, since exhaustion is
already known for each object of the compact subcategory.

No published target or imported file is modified, and no hypothesis is added.
