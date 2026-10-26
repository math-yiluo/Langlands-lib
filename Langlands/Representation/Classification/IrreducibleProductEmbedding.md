# Blockwise supercuspidal embeddings of normalized products

Proof author: Worker 157. Submission preparation and source verification:
Worker 472. The Lean implementation is reused unchanged from Worker 157's
shared draft revision 2.

The theorem
`Langlands.Classification.irreducibleProductEmbedding.{uF,uV}` proves exactly
`Langlands.Classification.IrreducibleProductEmbeddingTheorem.{uF,uV} F T`.
Its only parameters are a prime `p` with `Fact p.Prime`, an actual
`PadicField.{uF} p`, and arbitrary compatible topological data `T`.
This auxiliary unit constructs an actual injection from a normalized product
of arbitrary irreducible smooth complex GL factors to a normalized product
of their blockwise supercuspidal inductions. It does not assert finite length.
The original factor universe is independent of the field universe. Induced
carriers retain their actual function types in the maximum universe.

## Implemented argument

`FiniteTensor.externalMap_injective` chooses a complex-linear left inverse
of each injective factor map. The tensor of these left inverses is a left
inverse of the tensor map by `PiTensorProduct.map_comp` and `map_id`.
The left inverses need not be equivariant: equivariance of the forward map
comes from the existing `externalMap` construction. No finite-dimensionality
or finite-generation assumption is used.

`irreducible_supercuspidalProduct_embedding` applies the published
`CuspidalSupport.cuspidalEmbedding`, then
`padicLeviCuspidalFactorization` in any independently specified output
carrier universe. Normalized induction transports that factorization
by the existing `normalizedParabolicInducedEquiv`. Composing the original
injection with this equivalence gives the required actual intertwiner.
This avoids the universe restriction of the packaged
`glSupercuspidalEmbedding` statement.

`normalizedProduct_embedding_of_factor_embeddings` tensors the supplied
intertwiners, proves injectivity by the first lemma, and applies
`normalizedParabolicInducedMap_injective`. Both endpoints are the actual
objects of `normalizedProductInductionFunctor`.

`irreducibleProduct_embedding` chooses the preceding supercuspidal embedding
for every block, whose positive rank is supplied by `B.positive`, and applies
the product-injection lemma. Its endpoint is outer product induction of the
individual inner products. It includes the empty outer family. It does not
identify that endpoint with induction from flattened cuspidal data;
tensor regrouping, induction transitivity, coordinate normalization and
cuspidal induction finite length are subsequent obligations.

## Provenance and scope

This is an internal adapter derived from existing Library results, not a new
literature theorem. BZ77 Theorem 2.5 and Example 2.7, printed p.447,
PDF page 8, supply the mathematical
cuspidal-embedding input; the existing factorization theorem translates its
Levi data into supercuspidal block factors. Casselman 1995 Proposition 2.4.4,
printed p.28, gives the induction-injectivity principle implemented by the
published pointwise map. These original passages were read directly.

The eventual consumer is Henniart 2002 §2.5, printed pp.594–595, whose actual
upper-parabolic normalized product has finite length for arbitrary
irreducible smooth factors. That passage and Casselman Corollaries 6.3.7–6.3.8,
printed pp.59–60, were read directly. This unit proves only the embedding
step and preserves the Library's positive-half upper-parabolic covariance
and right-translation action. It uses no general finite-length preservation
or finite-generation theorem.

Retained registered originals:

- `bernstein-zelevinsky-1977-induced-i`, SHA256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
- `casselman-1995-admissible-representations`, draft 1 May 1995, SHA256
  `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
- `henniart-2002-characterization`, SHA256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
