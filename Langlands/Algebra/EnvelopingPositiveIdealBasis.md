# PBW coordinates of the positive right ideal

Let the ambient Lie algebra be the commutator Lie algebra of a
finite-dimensional associative algebra over a characteristic-zero field.
Fix a basis of eigenvectors for one adjoint operator with integral weights.
The supplied Lie maps send their chosen bases to the zero-weight and
positive-weight parts, respectively, of this ambient basis.

Restricting the ordered Lie basis to a subset of its indices preserves
their order. Under the corresponding Lie inclusion, the ordered
enveloping monomial has exponents extended by zero. Coordinates
supported entirely in nonpositive directions vanish on the span of
monomials with positive letters by linear independence.

The positive right ideal lies in that span. Multiplying by a positive
generator changes only the initial positive word of a PBW monomial.
The resulting word in the positive enveloping algebra has zero
augmentation, so it expands into ordered monomials with at least one
positive letter. An element of the zero-weight enveloping algebra whose
image lies in the positive right ideal must be zero. The zero-weight Lie
directions preserve the positive directions under the bracket, yielding
left stability of the ideal under the Levi enveloping algebra.
`relativeEnvelopingDecomposition_of_weight` assembles these facts with
the existence of a zero-weight representative modulo the ideal for
each ambient central element.

This derived PBW argument controls the enveloping centre on Levi
constant-term slices. Langlands (1979), Lemma 4, states automorphy of
those slices and gives references for local Hecke admissibility.
See printed p. 204 (Corvallis Part I, PDF p. 199). The registered source is
`langlands-1979-notion-automorphic-representation`, SHA-256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
