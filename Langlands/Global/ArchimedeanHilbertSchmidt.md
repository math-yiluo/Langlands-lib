# Actual archimedean Hilbert-Schmidt group norm

## Domain and finite-dimensional Hilbert space

Let `K : Type u` be a field with `NumberField K`, with arbitrary universe `u`,
and let `n : ℕ`. The source throughout is the actual completion-based group
`Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)`. The construction
imports the published `Langlands.Global.ArchimedeanComplexification` and
`Langlands.LinearAlgebra.InverseAdjointModel`.

Put `I = ArchimedeanComplexIndex K n`, namely `Fin n × ArchimedeanPlaceIndex K`.
The latter place index is the disjoint union of the real and complex infinite
places. `ArchimedeanHilbertIndex K n` is `Unit ⊕ (I ⊕ I)` and
`ArchimedeanHilbertSpace K n` is the actual complex Euclidean space on that
index. Its norm, inner product, completeness and finite-dimensional instances
are Mathlib's existing Euclidean ones. The inner product is the standard sum
of conjugate-coordinate products. The theorem
`finrank_archimedeanHilbertSpace` proves the complex dimension formula

\[
 \dim_{\mathbb C}E=1+2n\,\#\operatorname{ArchimedeanPlaceIndex}(K).
\]

The proof computes the cardinalities of the sum and product indices. No
positive-rank hypothesis is imposed; the scalar coordinate remains at rank zero.

## The actual representation and its intrinsic properties

Write `A(g) = infiniteAdelicComplexGL K n g`. This published continuous
homomorphism takes the actual completion-based group to the block diagonal
complex matrix of all local matrices: real-place matrices are included into
complex matrices, and complex-place matrices retain their complex entries.
It is a closed embedding into complex GL, and it sends
`standardInfiniteCompact K n` into the matrix unitary group.

`infiniteAdelicHilbertRepresentation` composes this map with the published
`inverseAdjointRepresentation`. It is a bundled continuous monoid
homomorphism to the full space `E →L[ℂ] E` of continuous complex-linear
endomorphisms. Every value is invertible, since the homomorphism sends `g⁻¹`
to a two-sided inverse of its value at `g`. Its matrix in the standard
orthonormal basis is `infiniteAdelicHilbertMatrix`, namely

\[
 \sigma(g)=\operatorname{diag}(1,A(g),(A(g)^{-1})^H),
\]

where `H` is conjugate transpose. The theorem
`infiniteAdelicHilbertRepresentation_apply` states that its coordinate action
is multiplication by this matrix. The monoid laws and continuity are obtained
by composition. The inverse-adjoint product law in the imported generic model
uses the fact that inversion and conjugate transpose each reverse products.

`isClosedEmbedding_infiniteAdelicHilbertRepresentation` composes the closed
embedding into complex GL with the generic model's closed embedding into
**all** complex continuous endomorphisms. Thus singular endomorphisms are
included in the ambient space of the closed-image assertion. The generic
proof embeds a unit together with its inverse, then uses an injective
finite-dimensional real-linear block map and adds the scalar block. No
closure or faithfulness certificate is assumed. The separate exports
`continuous_infiniteAdelicHilbertRepresentation`,
`infiniteAdelicHilbertRepresentation_injective`, and
`isClosed_range_infiniteAdelicHilbertRepresentation` give continuity,
faithfulness and closed range. Faithfulness is stronger than the source's
finite-kernel requirement.

For `g ∈ standardInfiniteCompact K n`, the theorem
`infiniteAdelicHilbertRepresentation_mem_unitary` proves that the actual
endomorphism belongs to `unitary (E →L[ℂ] E)`.
`infiniteAdelicHilbertRepresentation_inner` gives preservation of the complex
inner product for all `x y : E`. These follow from the published local
orthogonal/unitary characterization and the generic inverse-adjoint
unitarity theorem. In particular the Hilbert structure is invariant under
the published standard compact.

## Trace normalization and finite coordinates

The auxiliary function `infiniteAdelicLocalEntrySq` is the concrete finite sum

\[
 S(g)=\sum_{v\text{ real}}\sum_{i,j}|A_v(g)_{ij}|^2
      +\sum_{v\text{ complex}}\sum_{i,j}|A_v(g)_{ij}|^2.
\]

Here the local matrices are exactly `ArchimedeanGL.realMatrix` and
`ArchimedeanGL.complexMatrix` applied after `archimedeanGLCoordinates`.
The indices `i,j` range over `Fin n`. Each complex place contributes one
complex block, with no factor of two from real-coordinate conventions.

`infiniteAdelicHilbertNormSq` is defined directly as

\[
 Q(g)=\operatorname{Re}\operatorname{tr}_{\mathbb C,E}
        (\sigma(g)^*\sigma(g)),
\]

using `LinearMap.trace` and the actual Hilbert-space adjoint, which is `star`
on continuous endomorphisms. Multiplication here is operator composition.
`infiniteAdelicHilbertNormSq_eq_generic` identifies this definition with the
published generic squared Hilbert-Schmidt norm. That generic trace identity
computes the linear trace in the standard orthonormal basis and uses the
star algebra equivalence from matrices to Euclidean endomorphisms.
`infiniteAdelicHilbertNormSq_eq_sum` consequently identifies `Q(g)` with the
sum of squared absolute values of all entries of
`infiniteAdelicHilbertMatrix K n g`.

`infiniteAdelicHilbertNormSq_eq` proves the usable local formula

\[
 Q(g)=1+S(g)+S(g^{-1}).
\]

Its proof expands the generic three-block square formula, uses the
homomorphism's preservation of inverses, and applies the published
`infiniteAdelicComplexGL_sum_sq` twice. The scalar block gives exactly one;
conjugation and interchange of finite indices preserve the inverse-block sum.
`one_le_infiniteAdelicHilbertNormSq` transfers the generic lower bound, which
comes from nonnegativity of the squared entries.

`infiniteAdelicHilbertNorm` is defined as `Real.sqrt Q(g)`.
`infiniteAdelicHilbertNorm_eq_trace` displays the actual source-style trace
normalization, and `infiniteAdelicHilbertNorm_eq_generic` identifies it with
the generic norm at `A(g)`. The theorem `infiniteAdelicHilbertNorm_sq` states

\[
 \|g\|_{\mathrm{HS}}^2=1+S(g)+S(g^{-1}).
\]

The proof squares the square root using the lower bound on `Q`.
`one_le_infiniteAdelicHilbertNorm` and `infiniteAdelicHilbertNorm_pos` prove
that the norm is at least one and strictly positive.
`continuous_infiniteAdelicHilbertNorm` transports continuity of the generic
norm along the actual continuous complexification.
`infiniteAdelicHilbertNorm_inv` exchanges the two local sums and proves
inversion symmetry. `infiniteAdelicHilbertNorm_rank_zero` reduces the local
sums to empty sums and proves that the rank-zero norm is exactly one.

## Original source and derived choices

A. Borel and H. Jacquet, *Automorphic forms and automorphic representations*,
in *Automorphic Forms, Representations and L-Functions*, Proceedings of
Symposia in Pure Mathematics 33, Part 1 (1979), pp. 189–202, §1.2, printed
pp. 189–190, one-based PDF pages 184–185. The later motivation is §4.2(d),
printed p. 195, one-based PDF page 190.

Registered source: `borel-jacquet-1979-automorphic`. Retained original:
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`.
SHA256: `3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
The cited pages were read directly. No source errata note was present in the
Library or shared notes; the retained volume README contained no errata.

Section 1.2 uses the square-root trace norm of a finite-dimensional complex
representation with finite kernel and image closed in the endomorphism
space, with a Hilbert structure invariant under the selected maximal compact.
Its next-page remark adjoins the inverse-adjoint representation. The present
construction implements that route for the actual archimedean general
linear group, and proves invariance under `standardInfiniteCompact`.
The maximality of that compact is a separate obligation; this module proves
no maximal-compactness theorem.

The scalar summand is an explicit derived normalization. It preserves the
homomorphism and compact invariance, contributes one to the squared norm,
and ensures positivity even in rank zero. The closed embedding and
faithfulness after this augmentation are proved by the composed constructions,
not inferred from an assumed source norm. The chosen index, Euclidean
coordinates, composition interfaces and local formula are derived
formalization choices, not additional claims attributed to the source.

The term “group norm” denotes this representation norm; it is not asserted
to be a metric norm vanishing at the identity. Section 4.2(d) motivates its
future use on each finite adelic slice. Polynomial comparison with
`matrixHeight` and equivalence of growth predicates remain downstream
statements and proofs. Neither estimate is assumed or asserted here.
