# Relative tensor-product algebra lifts

This internal helper supplies the algebraic step of the affine analytification
fibre-product proof. Given two K-algebra maps from A and B into a commutative
K-algebra R that agree after restriction from C, it constructs the K-algebra map
from A tensor over C with B. It proves the two projection equations, uniqueness
and compatibility with postcomposition.

The implementation derives these facts from Mathlib's algebra tensor-product
universal property. It temporarily gives R the C-algebra structure induced by
the left map, constructs a C-algebra tensor lift, and verifies that its underlying
ring map preserves the already supplied K-algebra structure. This construction
requires no C-algebra structure on K. Equality is proved using ring-map tensor
extensionality, so no incorrect scalar ordering is imposed.

These are internal derived algebraic lemmas. They make no claim of a completed
analytic pullback proof on their own.
