# Adjoint weights under restriction between split tori

Author: Worker 1317.

This is an internal construction and its API, derived from the published
all-test-algebra adjoint weight spaces, their internal direct-sum decomposition
for split tori, and the component projections in `Rational.GenericLieWeights`.
No reductivity or maximality assumption is used.

For an affine group scheme over any affine base `Spec R` and a homomorphism
`f : T' ⟶ T` of commutative group schemes, `rootRestriction f i` sends each
actual root `χ` of the action `i : T.toGrp ⟶ G` whose restricted character is
nonzero to the actual root `f ≫ χ` of the restricted action. The source subtype
retains both root membership and the nonvanishing condition. Its target root
membership follows from the published `weightSpace_le_comp`: a nonzero
original weight space remains a nonzero subspace of the restricted one. This
map requires no splitting, field or finite-type assumption.

The comparison and surjectivity results below concern an affine group scheme
locally of finite type over an arbitrary field. Both acting commutative group
schemes are assumed split tori; their connecting homomorphism is arbitrary.

For `f : T' ⟶ T` and `i : T.toGrp ⟶ G`,
`weightSpace_comp_eq_iSup` identifies the weight space of a character `ψ` for
the restricted action with the supremum of the original weight spaces indexed
by characters `χ` satisfying `f ≫ χ = ψ`. To prove this, the implementation
projects onto the restricted weight space. This projection fixes vectors in
every original summand with that restricted character and kills vectors in
every other original summand. The original weight spaces span the Lie algebra,
so induction on their supremum proves one inclusion. The published
`weightSpace_le_comp` gives the reverse inclusion.

`mem_roots_comp_iff` deduces that a restricted character is a root exactly when
it is nonzero and is the restriction of an original root. A nonzero restricted
weight space forces some summand in the displayed supremum to be nonzero; its
original character cannot be zero because its restriction is nonzero. The
converse follows from the inclusion of the original weight space in the
restricted one.

`rootRestriction_surjective` uses this characterization to prove that the
constructed map reaches every root of the restricted split-torus action.

`neg_mem_roots_comp` then transports an explicit negation-stability hypothesis
for the original roots to the restricted roots. It pulls back the negative of
an original root and uses additivity of character pullback.

These results implement the same-field split-torus restriction step needed in
the absolute-to-relative root route. They do not prove the existence of
opposite absolute roots, the existence of a split maximal torus, or compatibility
of actual weight spaces with scalar extension. In particular, they do not
prove `RelativeRootNegationStatement`.

The refinement helper `submodule_eq_iSup_of_refinement` is public so that
`WeightBaseChangeComparison` can reuse the same spanning-family argument. Its
statement and proof are unchanged.
