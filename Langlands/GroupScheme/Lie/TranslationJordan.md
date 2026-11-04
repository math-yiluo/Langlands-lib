# Jordan components of actual infinitesimal translation

This module constructs a semisimple component of every actual Lie-kernel
point of an affine group scheme over a perfect field. It proves that every
actual finite matrix representation sends that point to the canonical additive
Jordan semisimple component of its original differential. The field has an
arbitrary universe. No smoothness, connectedness or finite-type premise is
required. Local finiteness of translation, used in the construction, is proved
over every field.

## Finite coefficient spaces and polynomial translation

`translationCoefficientSpan` is the span over the ground field of all entries
of the universal coefficient matrix of an actual representation on `Fin n`.
`coordinateMatrix_mem_translationCoefficientSpan` places each entry in that
span. `translationCoefficientSpan_invariant` uses `D(U) = M U`, with `D` the
actual infinitesimal left-translation derivation and `M` the actual tangent
matrix: each derivative is a ground-field linear combination of entries of
`U`. Span induction proves invariance for every vector in the span.
`translationCoefficientSpace` packages that invariant span with its finite
dimension, obtained from the finite range of its coefficient indexing map.

`coordinateMatrix_translationDerivation_aeval` proves
`P(D)(U) = P(M) U` for every ground-field polynomial. It expands both polynomial
evaluations into their coefficient-weighted powers, applies the existing
identity `D^m(U) = M^m U`, and rearranges finite sums.

`translationDerivation_isLocallyFinite` applies the existing actual coalgebra
coefficient theorem: every coordinate lies in the coefficient span of some
actual finite representation. Its finite invariant coefficient space therefore
witnesses local finiteness for that coordinate. No finite-type assumption on
the group is introduced.

## The actual semisimple Lie element

Over a perfect field, `semisimpleKernel` evaluates at the actual identity the
semisimple derivation component of the translation derivation. The preceding
local-finiteness theorem supplies the construction's premise; the imported
locally finite derivation theorem supplies its Leibniz identity.

`tangentMatrix_semisimpleKernel` proves, for every actual representation on
`Fin n`, that the linear endomorphism of the constructed tangent matrix equals
`jordanSemisimplePart` of the original tangent matrix's linear endomorphism.
The proof takes one common Jordan polynomial for the finite coefficient-space
restriction of `D` and the endomorphism defined by `M`. Finite Jordan uniqueness
identifies its evaluations with both canonical semisimple parts. Compatibility
of the global part with finite invariant subspaces and polynomial intertwining
through the coefficient-space inclusion identify the semisimple derivation's
values on every entry of `U` with `P(D)(U)`. The polynomial translation identity
and evaluation of `U` at the identity then give `P(M)`. Matrix-to-endomorphism
polynomial compatibility proves the stated equality.

`isGeometricallySemisimpleMatrix_of_isSemisimple` proves that ordinary matrix
semisimplicity over a perfect field implies geometric semisimplicity. Its
squarefree minimal polynomial is separable by perfection. The existing
separable-annihilator criterion then transports semisimplicity to the algebraic
closure. Applying this criterion to the canonical components in every
representation proves `isSemisimpleElement_semisimpleKernel`, using exactly the
published representation-tested geometric predicate.

## Provenance and scope

This is derived content from actual universal representation coefficients,
translation derivations and their power formula, the coalgebra coefficient
span theorem, finite Jordan uniqueness and common polynomials, and compatible
global Jordan derivations. The geometric step uses Mathlib's perfect-field
squarefree/separable equivalence and the existing separable-annihilator lemma.
No additional algebraic-group structural theorem is assumed. Perfection
remains an explicit premise for `semisimpleKernel` and its properties. These
results do not prove the required centralizer inclusion or noncentrality of
the constructed element, nor Cartan generation.
