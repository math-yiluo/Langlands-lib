# Signed diagram of actual normalized induction and Jacquet terms

Internal construction by Worker 194 on actual subgroup families, using the
separately owned normalization adapter of Worker 23.

For removed-root sets `s`, `termObject A s` is the genuine normalized
`inductionJacquetFunctor` object. The explicit coinvariant action, induced-function
carrier and right-translation action avoid expensive category projections;
`termObject_eq` proves definitional equality with the actual functor object. The subgroup hypotheses are a semidirect
decomposition `P(s) = M(s) U(s)`, closedness of each `U(s)`, unimodularity in
the named modulus sense, antitonicity of `P` and monotonicity of `U`.
Unimodularity is retained in-book proof work, not an allowed external premise
for final theorem closure.

`transition` conjugates the existing canonical subgroup transition with
`inductionJacquetTermIso`. Both comparisons preserve functions, and
`transition_eval` states that evaluation at `g` applies the actual quotient map
`[v]_(U(s)) ↦ [v]_(U(t))`. Identity and composition are proved by the comparison
and the existing quotient-map laws. `diagramEquivalence` records this
comparison with all maps, rather than only identifying coordinate objects.

The existing increasing cut basis supplies the exterior signs. The homogeneous
action is the product of the genuine normalized representations.
`differential` uses the existing signed sum and is proved equivariant.
`differential_square` follows from the proved diagram laws, and
`degreeEquiv_differential` compares the actual signed maps, retaining their
exterior coefficients. Finite products of smooth representations prove
`degree_isSmooth`, with no finite-length condition on the input module.

This construction does not realize a reductive group's standard-subset family,
prove exactness, define its support category, or assert any consequence about
terminal cokernels, finite length or irreducibility.
