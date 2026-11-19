# Pullback and gluing of local-system isomorphisms

These helpers implement the comparison of trivializations in Conrad,
*Reductive group schemes*, proof of Corollary B.3.6. A lift of a test scheme
to the restricting base identifies it with an object of the original over
category using the identity of its domain. The component of a restricted
isomorphism can therefore be transported to the test scheme. Naturality on
compatible lifts gives pullback of isomorphisms of restrictions over the
fixed original base. Pullback of an isomorphism given by a locally constant
family amounts to pulling back that family.

For a map `B ⟶ S` and an étale cover of `B`, consider the full subcategory
of test schemes over `B` that lift to a cover member. It is cover dense.
Pairwise agreement on the fibre products over `B` makes the isomorphisms
evaluated on a test scheme independent of its lift. They define a natural
isomorphism on that full subcategory. Mathlib's extension theorem for
cover-dense subsites gives the isomorphism of the two sheaves restricted to
`B`.
