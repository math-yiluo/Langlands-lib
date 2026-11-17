# Galois compatibility of actual character spaces

This internal derived module develops the all-test compatibility needed in the
proof of Milne, *Algebraic Groups* (2017), Theorem 12.30. It does not yet prove
that theorem.

A vector in a universal character space satisfies the character equation on
every test scheme. The proof first passes from affine coefficients to global
sections through the canonical affine section isomorphism, and then pulls back
along the map to a chosen affine coordinate model of the group. Conversely,
the equation on all tests includes the universal affine test and implies
membership in the character space.

For a representation defined over the original field, the point matrix is
unchanged when the point is viewed over a test scheme with its structure map
twisted by a field automorphism. This follows from the published base-change
matrix formula and the canonical descent point comparison. The scalar map
of the twisted test is the original scalar map composed with the field
automorphism. The existing character transport formula then proves that
coefficientwise conjugation of a character vector belongs to the conjugated
character space.

The argument uses arbitrary test schemes and hence arbitrary affine test
algebras, including nonreduced ones. It assumes affineness but no smoothness,
reducedness, multiplicative-type condition or Galois extension hypothesis.
The provenance is internal and derived: these are compatibility lemmas for
the Library's actual coordinate definitions, corresponding to the Galois
weight-space compatibility used in Milne's proof on printed page 242.
