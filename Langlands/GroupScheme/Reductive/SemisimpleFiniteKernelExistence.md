# Existence of a semisimple representation with finite kernel

`IsConnectedReductive.exists_semisimple_finiteKernel` proves the forward
implication of the published reductivity criterion. It works over every field,
without a perfectness assumption: a connected reductive group admits an actual
representation on a finite coordinate space whose nonzero simple stable
subspaces sum to the whole space and whose full scheme-theoretic kernel is
finite over the field.

Choose a closed faithful representation by the published affine linear
embedding theorem. Its existing `SimpleFactorFamily` supplies finitely many
nonzero simple actual subquotients, together with nilpotent deviation from the
identity for the original representation on their common kernel, on all scheme
tests. Form their direct sum and reindex its coordinates to `Fin n`. The
published direct-sum construction and the simple-image/spanning lemmas give
exactly the required supremum semisimplicity predicate.

On every point of the new representation's kernel, its reindexed matrix is the
identity. Evaluating the matrix entries at the reindexed coordinates recovers
identity for the factor sum before reindexing. The factor-family nilpotence
then shows that this closed normal kernel acts unipotently in the original
closed faithful representation. The arbitrary-field finite-normal-subgroup
helper proves that the full kernel is finite. That helper passes to an
algebraic closure only for this finiteness argument, so the proof does not need
simple factors to remain simple after field extension.

Provenance: a derived composition-factor proof of the forward implication in
J. S. Milne, *Algebraic Groups* (2017), Proposition 21.60, printed p. 442
(registered source `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`).
This proof uses the Library's composition-factor infrastructure rather than
the source's central/derived product route. Semisimplicity uses the source's
Definition 4.15, printed p. 90: being the sum of simple subrepresentations.
The retained official 2017 errata snapshot has no correction for p. 442.
