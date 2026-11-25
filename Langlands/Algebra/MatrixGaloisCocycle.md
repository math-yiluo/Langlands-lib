# Actual scalar cocycles of semilinear matrix descent

This module starts with an actual semilinear Galois action on a full matrix
algebra. Its coefficient-linear part is an actual algebra automorphism and hence
is realized by an actual invertible matrix using the published
`MatrixAlgebra.exists_unit_conj_of_algEquiv`. Those matrices express the complete
semilinear action, with its specified field automorphism on every coefficient.

The products of these actual matrices realize the same conjugation action as the
matrix of the product Galois automorphism. The published scalar-ambiguity theorem
therefore supplies an actual unit scalar defect. The chosen defect satisfies the
multiplicative scalar two-cocycle identity by the generic associativity lemma in
`ScalarTwoCocycleLifts`. The coefficient action on general-linear matrices and the
injectivity, centrality and equivariance of the scalar embedding are proved
explicitly. The nonempty finite matrix index and fields are arbitrary; finiteness
or Galoisness of the field extension is not required for these identities.

No Brauer-group operation or actual-algebra splitting criterion is assumed by
this module. A later consumer must construct its actual semilinear action from the
supplied algebra or descent datum and prove the necessary splitting comparison.
