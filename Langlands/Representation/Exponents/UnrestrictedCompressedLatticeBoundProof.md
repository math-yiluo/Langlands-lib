# Unrestricted compressed-lattice coefficient bound

`Langlands.unrestrictedCompressedLatticeBound.{uG,uV,uI}` proves the whole
`Langlands.UnrestrictedCompressedLatticeBoundStatement` at independent group,
carrier and index universes. This is an internal derivation from existing
finite-dimensional compression results.

`UnrestrictedLatticeBound.endNorm_pow_le` uses induction and
`EndomorphismBound.endNorm_mul_le`. For an endomorphism `f`, the radius
`endNorm f + 2` exceeds one. The factor `endNorm 1 + 1` handles the zeroth power
without assuming that the vector space is nonzero.

`UnrestrictedLatticeBound.exists_apply_le_prod` chooses these radii for the
finitely many coordinate generators. It applies
`CompressedLatticeBound.endNorm_le_prod_of_pow_bounds` to bound the whole
multiplicative lattice, then `EndomorphismBound.exists_apply_le_endNorm` to
evaluate any vector and algebraic dual functional. Adding one to the resulting
nonnegative constant makes it positive. The radii precede the coefficient
pair in the quantifiers; the constant may depend on that pair. This argument
also covers an empty coordinate type and the zero vector space.

For the representation-theoretic theorem, admissibility makes the space of
`K`-fixed vectors finite-dimensional. The explicit factorization and
conjugation hypotheses supply multiplicativity through
`Jacquet.compressedAction_mul_of_factor`. Finally,
`StrictCartanBound.dual_apply_eq_compressedAction` identifies the original
coefficient with the compressed coefficient because the functional is fixed
by `K`. No eigenvalue, Jacquet-exponent, or finite-length hypothesis is used.

This proof retains all geometric premises of the statement. It does not prove
that a suitable compact subgroup or lattice exists for an actual reductive
group and does not compare the product bound to a matrix norm.
