# Real tensor splitting of a totally real number field

This module constructs the real algebra isomorphism

\[
\mathbb R\otimes_{\mathbb Q}E \;\simeq_{\mathbb R}\;
\prod_{\tau:E\to\mathbb R}\mathbb R,
\qquad r\otimes x\longmapsto (\tau\longmapsto r\tau(x)),
\]

for any totally real number field `E`. All products in this module are the
actual function rings indexed by ring embeddings. The tensor product is the
actual algebra tensor product. Bijectivity is proved from bases; no splitting
isomorphism is assumed.

## Provenance and scope

This is an internal construction from the pinned Mathlib number-field and
tensor-product APIs. Its inputs are `Field E`, `NumberField E`, and
`NumberField.IsTotallyReal E`; `E` may inhabit any universe. The principal
definition is `Langlands.Global.TotallyReal.tensorEquiv`.

The existing Mathlib results used below are
`NumberField.canonicalEmbedding.latticeBasis`,
`NumberField.canonicalEmbedding.latticeBasis_apply`,
`NumberField.IsTotallyReal.complexEmbedding_isReal`,
`NumberField.ComplexEmbedding.IsReal.coe_embedding_apply`, and
`NumberField.Embeddings.card`. They supply the complex evaluation basis, the
factorization of complex embeddings through the real numbers, and the count of
embeddings. This module derives the real tensor splitting from those results;
it invokes no new external theorem or source-specific assertion.

This field-algebra prerequisite will support assembling the existing real-place
charts of the Harris algebra. It does not itself construct that matrix-algebra
identification, its involution comparison, or any Shimura scheme.

## Embeddings and the evaluation basis

`realComplexEmbeddings` identifies real embeddings with complex embeddings.
The forward map composes with the inclusion of the reals into the complex
numbers. Total reality supplies the inverse real embedding, and the existing
coercion identity proves that the two maps are inverse.

`evaluation` is the rational algebra homomorphism sending `x` to the function
`τ ↦ τ x`. It is defined by the product of ring homomorphisms and the canonical
rational algebra structure. `evaluation_apply` is its evaluation formula.
The definition and this formula do not require total reality.

The evaluated integral-basis vectors form `evaluationBasis`, a real basis of
the real function space. The proof first maps the real function space linearly
to the complex function space by the embedding equivalence and real-to-complex
coercion. Under this map, the evaluated integral-basis vectors become Mathlib's
complex canonical-embedding lattice basis. Restricting that basis's linear
independence to real scalars and pulling independence back along the linear
map proves independence of the real vectors. The number of vectors equals
the dimension of the real function space: both are the degree of `E` over the
rationals, using the integral basis and the embedding-count theorem.
`basisOfLinearIndependentOfCardEqFinrank'` therefore supplies the basis.
`evaluationBasis_apply` records its vectors explicitly.

## Tensor evaluation and its inverse

`tensorEvaluation` extends `evaluation` along the rational-to-real scalar map
using `AlgHom.liftEquiv`. It is a real algebra homomorphism with the exact
pure-tensor formula

\[
\operatorname{tensorEvaluation}(r\otimes x)(\tau)=r\tau(x),
\]

proved by `tensorEvaluation_tmul`. These definitions and formulas do not need
total reality.

`tensorEvaluation_bijective` compares its underlying linear map with the basis
equivalence from the real scalar extension of the rational integral basis to
`evaluationBasis`. Equality is checked on each basis vector: the source vector
is `1 ⊗ x`, whose evaluated image is precisely the target basis vector. The
basis equivalence is bijective, so the tensor evaluation is bijective.

Finally, `tensorEquiv` is `AlgEquiv.ofBijective` applied to this map and proof.
Its inverse and the two inverse identities are part of the resulting algebra
equivalence. The inverse is noncomputable; the construction provides no chosen
closed-form interpolation coefficients. `tensorEquiv_tmul` states the same
pure-tensor formula for this equivalence.
