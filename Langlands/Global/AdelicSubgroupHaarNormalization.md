# Independence of normalized subgroup measures from the initial Haar measure

For a closed evaluated adelic subgroup with its actual discrete principal
subgroup, `normalizedRationalQuotientHaarMeasureFrom` starts with any
specified measure on that subgroup and divides its fundamental-domain
quotient measure by its total mass. `normalizedHaarMeasureFrom` scales
the ambient measure by the same inverse mass. These definitions do not
assert probability or invariance for an arbitrary measure.

For any genuine initial Haar measure, both constructions equal the
previous intrinsic constructions using `Measure.haar`. Thus a change of
initial Haar measure changes neither normalized ambient Haar nor the
normalized quotient measure. The proof uses uniqueness of Haar up to a
strictly positive finite scalar and cancels that scalar against the
inverse fundamental-domain mass. The generic rescaling laws hold even
without compactness. With a compact actual rational quotient the
normalized quotient is a probability measure by the earlier construction.

This is an internal derivation supporting the mass-one convention of
Moeglin--Waldspurger, I.1.13, first paragraph, printed p.18, in
`05.1_pp_1_18_Hypotheses_and_general_notation.pdf`. The actual number-field
subgroup discreteness and closedness hypotheses are retained. The
result establishes independence from the initial Haar choice; it does
not identify different subgroup functors, compare arbitrary rational
presentations, or infer a right-invariance premise from an algebraic
determinant.
