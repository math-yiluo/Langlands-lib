# Filtered Cartan symmetrization on compact-stable modules

Author: Worker 94. This is an internal algebraic specialization of filtered
direction removal to the actual archimedean matrix Lie algebra and its Cartan
decomposition. The field `K` may lie in any universe, and the rank is any natural
number; neither a number-field hypothesis nor a positive-rank hypothesis is
needed.

`cartanSymmetrizationSpan d` is the image of the actual Cartan symmetric monomial
span of length at most `d` under symmetrization along the actual complementary
inclusion. The theorem `retractedSymmetrizationSpan_cartan` identifies this with
the generic retracted symmetric image for inclusion composed with projection.
Both projection and inclusion preserve monomial bounds. Inclusion followed by
projection is the identity on the Cartan symmetric algebra, which proves the
reverse image inclusion. Thus these images increase with `d`, contain the unit
and lie in the genuine enveloping degree pieces.

Let `V` be any genuine module over the actual enveloping algebra, with a
compatible complex scalar action. If its complex subspace `W` is stable under
every actual complex compact Lie generator, then
`cartanSymmetrizationSpan_smul_eq` proves that the bounded Cartan action span on
`W` equals the full filtered enveloping action span `F_d W` for each `d`.
The proof uses the generic filtered-spanning theorem: removing the actual Cartan
projection leaves an actual compact direction, and the assumed compact-generator
stability is exactly the stability of the generic removed-direction subspace.

This result asserts algebraic spanning, without assuming PBW injectivity or
finite dimension. Invariant tensor lifting, central finite generation and
automorphic differential growth require further arguments.
