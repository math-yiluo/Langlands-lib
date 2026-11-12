# Actual conjugate-factor isomorphisms

This internal construction by Worker 166 compares the actual scalar extensions
of the descended stabilizer-field group with the original indexed factors,
compatibly with the original descended inclusion.

Equality of the all-test ranges of a Galois-transported factor inclusion and
the factor inclusion selected by its canonical index gives an actual source
isomorphism `galoisFactorIso`. Its composite with the selected inclusion is
exactly the original transported inclusion. This first construction only needs
the supplied smooth affine almost-simple product presentation after a field
extension and an automorphism over the original field.

For an embedding of the stabilizer field into the upper Galois field, the
previously chosen extension automorphism restricts to that embedding. The
corresponding maps of spectra therefore agree. The standard pullback
comparison, the base change of the descended model's recovery isomorphism,
and the preceding source isomorphism give `embeddingConjugateFactorIso`.
It identifies the actual embedding scalar extension of the actual descended
group with the factor selected by `factorIndexOfEmbedding`.

`embeddingAmbientIso` compares the ambient group pulled back along that
embedding with the original upper-field group. The homomorphism
`embeddingFactorInclusion` is precisely scalar extension of the actual
stabilizer-field inclusion, followed by this ambient comparison. The theorem
`embeddingConjugateFactorIso_hom_inclusion` says that the conjugate-factor
isomorphism followed by the original indexed factor inclusion equals this
actual homomorphism.

The proof retains the descended model's recovery equation. The generic
`comparison_descent_coherence` identifies the two ways of composing the
projection-compatible tower comparison with a change of base structure. It
compares their points on every relative test scheme and then their
projections to the original group. Applying this coherence and naturality of
the pullback comparison to the recovery equation proves the exact inclusion
identity. Thus the result identifies specified embedded factors, not only
abstract isomorphism classes.

The embedding constructions retain the arbitrary-Galois, affine and
finite-presentation assumptions of the stabilizer-field descent construction.
No almost-simplicity assumption on the original group is needed here, since
the embedding-index map is defined without its surjectivity premise. No
perfectness or finite-degree assumption on the upper extension is added.
An actual product Weil-restriction isomorphism and the final structure theorem
remain separate obligations.
