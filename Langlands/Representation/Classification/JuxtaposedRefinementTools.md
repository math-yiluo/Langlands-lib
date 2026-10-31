# Shared coordinates and factor equivalences for juxtaposed induction

This internal supporting module contains the coordinate and equivalence helpers
shared by the increasing-embedding and decreasing-quotient constructions for two
juxtaposed segment socles. It is derived from existing block-shape, twist and
ordered normalized-induction infrastructure. It asserts no segment constituent
existence or classification result. The code was extracted from Worker 1032's
initial-embedding draft, jointly adapted with Worker 167.

`index_index_eq_of_lt_iff` identifies the actual coordinate embeddings for a block
refinement with those of a flat block shape, assuming a lexicographic numbering
of the inner blocks and equal corresponding sizes. Its proof constructs the
resulting increasing self-map of `Fin n` and shows that it is the identity.
`val_finSigmaFinEquiv_fin_two` computes the flat index in a two-block refinement.

`twistCongrIso` transports a smooth representation along equality of twisting
characters. `segmentFactorTwistIso` combines consecutive determinant-power twists:
applying the twist with exponent `s` to the twist with exponent `a` gives the
factor with exponent `s + a`. The proof uses the existing twist composition
isomorphism and the additive identity for determinant-power characters.

`nonempty_cast_iso` compares a factor of a chosen representative of a twisted
cuspidal datum with the corresponding factor of the original representative.
Its hypotheses explicitly provide the equality of cuspidal data, both
representatives, a rank equality, and an isomorphism to the factor at exponent
`s + a`. The conclusion transports that factor along the rank equality and
identifies it with the chosen twisted representative's factor at exponent `s`.
The proof uses equality of supercuspidal isomorphism classes and twist functoriality.

`regroup_nonempty_iso` first applies the proved ordered-product regrouping
isomorphism with the supplied coordinate compatibility, then applies the outer
normalized-product functor to the supplied inner isomorphisms. Input carriers
retain universe `uV`; inner inductions and the outer factors use `max uF uV`.

The direct imports are `Segments`, `OrderedProductRegroupingProof`, and
`MinimalJacquetProof`. The last supplies the block-coordinate order lemmas; no
Jacquet formula or geometric-lemma result is assumed by these proofs. All
representation-theoretic inputs used here are proved lower infrastructure.
