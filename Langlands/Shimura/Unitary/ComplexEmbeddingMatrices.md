# Complex matrix factors labelled by CM embeddings

The input consists of the actual Harris signature charts `C` for an algebra
`A` over the quadratic totally complex extension `K/E` of a totally real number
field, a compatible CM section `Φ` with proof `hΦ`, and a finite `E`-basis `b` of
`A`. The algebra structures and the rational-to-real scalar tower are those of
`ComplexMatrixSplitting`. No separate complex splitting is supplied as input.

`ComplexMatrix.factorIndexEquiv` is a general algebra equivalence from functions
with values in a pair of algebras to functions on the original index set times
`Bool`. The true index selects the first factor and the false index selects the
second. Its inverse pairs the two values. The algebra laws and inverse laws are
verified by considering the two Boolean cases.

`HarrisSignatureCharts.embeddingMatrixEquiv` constructs

\[
  \mathbf C\otimes_{\mathbf Q}A
  \simeq_{\mathbf C}
  \prod_{i:K\hookrightarrow\mathbf C}M_n(\mathbf C).
\]

It composes the existing `complexMatrixEquiv`, the ordered-pair index
equivalence, and reindexing along `cmFactorEmbeddingEquiv Φ hΦ`. The factor
formula identifies the value at `cmFactorEmbedding Φ (τ, true)` with the first
old matrix factor at `τ`, and the false case with the second. This is proved by
the reindexing equivalence's evaluation identity.

`embeddingEvaluation i` is a ring homomorphism from `A` to the matrix algebra:
it includes `A` into its rational complex scalar extension and projects the
constructed splitting to the factor labelled by `i`. Its two factor formulas
are `C.evaluation a τ` and its entrywise complex conjugate, respectively.
The pure-tensor formula for the full equivalence is

\[
  \mathrm{embeddingMatrixEquiv}(z\otimes a)(i)
    =z\,\mathrm{embeddingEvaluation}(i)(a).
\]

The proof reduces every embedding to one of the two factors using surjectivity
of `cmFactorEmbeddingEquiv`, then applies the published pure-tensor formula for
`complexMatrixEquiv`.

The center compatibility theorem `embeddingEvaluation_center` proves

\[
  \mathrm{embeddingEvaluation}(i)(\mathrm{algebraMap}_{K,A}(k))
    =\mathrm{scalar}(i(k)).
\]

For a selected embedding this is the existing chart center formula. For the
conjugate embedding it follows by entrywise conjugation of that scalar matrix;
the proof checks diagonal and off-diagonal entries. Thus the embedding label
has the asserted algebraic meaning.

This is an internal reindexing and compatibility construction from
`ComplexMatrixSplitting`, `CMEmbeddingIndices`, and the center condition of
`HarrisSignatureCharts`. It retains the chart and basis dependence. The module
does not yet compare Galois-transformed individual matrix charts, prove their
conjugacy, or identify the scheme-cocharacter reflex stabilizer.
