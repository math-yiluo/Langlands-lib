# Finite presentation of affine dynamic inclusions

Workers 3483 and 286. Helpers for the arbitrary-base representability proof.

For an affine group over any commutative ring whose structure morphism is
locally of finite type, the actual closed inclusions of its parabolic,
centralizer and unipotent dynamic representatives are locally of finite
presentation. No smoothness or Noetherian assumption is imposed.

The proof uses the published finite-generation lemmas `negIdeal_fg`,
`offIdeal_fg` and `unipIdeal_fg` in `Dynamic.SmoothOverRing`, which need only
finite type of the coordinate algebra. Each canonical inclusion is the
spectrum of a quotient by the corresponding finitely generated ideal.
The surjective ring-map criterion gives finite presentation, and the
published coordinate isomorphism transfers this to the actual group.

These are internal intermediate consequences of published constructions and
ring lemmas for the proof of Conrad Theorem 4.1.7(1), not a new external
mathematical assertion. The parent target's Markdown records original-source
provenance. When the ambient group is locally of finite presentation, composing
these inclusions with its structure map also gives locally finitely presented
representatives. The global gluing is carried out in
[`BaseRepresentabilityProof`](BaseRepresentabilityProof.md).
