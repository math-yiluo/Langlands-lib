# PBW coordinates of the positive right ideal

Restricting the ordered Lie basis to a subset of its indices preserves
their order. Under the corresponding Lie inclusion, the ordered
enveloping monomial has exponents extended by zero. Coordinates
supported entirely in nonpositive directions vanish on the span of
monomials with positive letters by linear independence.

The positive right ideal lies in that span. Multiplying by a positive
generator changes only the initial positive word of a PBW monomial.
The resulting word in the positive enveloping algebra has zero
augmentation, so it expands into ordered monomials with at least one
positive letter. The zero-weight enveloping algebra is disjoint from
this span. Its commutators preserve the positive directions, yielding
the required stability under Levi operators. The construction
`relativeEnvelopingDecomposition_of_weight` assembles these facts
with the existence of a representative for every central element.

This gives the coordinate comparisons for the triangular
enveloping-centre argument in Langlands (1979), Lemma 4, printed p. 204
(Corvallis Part I, PDF p. 199). The registered source is
`langlands-1979-notion-automorphic-representation`, SHA-256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
