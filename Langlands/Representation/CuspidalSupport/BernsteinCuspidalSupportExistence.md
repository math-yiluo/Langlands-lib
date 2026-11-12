# Actual cuspidal support at the saturated carrier universe

This internal supporting unit proves the existing `BernsteinCuspidalSupportExistenceStatement` for a `BernsteinStandardFamily` with independent universes `uF` and `uV`. The representation, cuspidal datum and induction all use the same saturated carrier universe `max uF uV`. It adds no hypothesis to that target.

The implemented proof starts with the published arbitrary-carrier minimal nonzero Jacquet theorem. For an irreducible source, finite generation over the ambient group algebra and compactness of the actual parabolic quotient imply finite generation of this Jacquet module over the actual Levi group algebra. The compactness input is the published unconditional `BruhatTits.dynamicParabolicQuotientCompact`, through `compactSpace_leftQuotient_parabolic`.

The published `CuspidalEmbedding.exists_irreducible_quotient_of_finite` chooses an irreducible quotient in the same carrier universe. Proper inner Jacquet modules of this quotient vanish because the corresponding Jacquet maps are surjective and their source modules vanish. First adjointness turns the quotient map into an embedding of the irreducible original representation into normalized induction, using `CuspidalEmbedding.embedding_of_surjective_jacquet_map`.

The quotient action is transported by the canonical `leviRationalPointHomeomorph` to the represented standard Levi scheme. Cancellation of the inverse pullback gives an actual smooth isomorphism to the original quotient. Applying normalized induction to this isomorphism preserves the embedding. Cuspidality and irreducibility of the transported action are retained, so these are genuine `BernsteinCuspidalDatum` witnesses.

`exists_bernsteinCuspidalDatum_induction_subrepresentation` proves this embedding presentation. `bernsteinCuspidalSupportPresentation` chooses one datum and retains its actual subrepresentation witness. `bernsteinCuspidalSupportExistence` then regards the embedding as a subquotient presentation, proving the existing support-existence proposition.

The provenance is internal: this is a composition of the Library's minimal Jacquet, finite-generation, quotient-existence, compactness, first-adjointness and canonical-transport results. It reuses the proof route of `RationalCuspidalEmbeddingProof` while avoiding that theorem's raised carrier universe. It does not assert support uniqueness, induction–Jacquet support comparison, fixed-Levi block embeddings, or the full Bernstein characterization.

The instances introduced here have explicit names specific to this module so that
combined imports retain distinct declarations. Their types, bodies and instance
scopes are unchanged.
