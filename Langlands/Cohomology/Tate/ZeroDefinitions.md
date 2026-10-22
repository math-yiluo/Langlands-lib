# Degree-zero Tate cohomology

Author: Worker 45.

This construction compares Mathlib's actual `tateCohomology A 0` with
`A^G / N_G A`. The denominator is the range of the actual sum of the group
action, with codomain restricted to invariant vectors. It is not supplied as
data. The short complex comparison and the kernel and cokernel certificates
inside the construction are proved.

`Pairing A B C` consists of an actual scalar-bilinear coefficient map and its
equivariance proof. Its restriction to invariant vectors sends a norm in either
argument to a norm in the target, when the other argument is invariant. The
proof expands the norm into the sum of the group action and uses equivariance.
These two certificates define `quotientProduct` through the actual quotient
universal property. `cupZero` transports that product back to Mathlib's Tate
cohomology. No cohomological product or compatibility law is an input.

The commutative scalar ring, finite group, and representation have the
arbitrary carrier universe supported by the pinned Tate interface. In
particular, `IntegralScalar` is `ULift.{u} ℤ`, `integralScalarEquiv` is the
explicit ring equivalence to the integers, and `integralTrivial` is the actual
trivial representation on that ring.

The source is Jean-Pierre Serre, *Local Fields*, Greenberg translation,
Springer GTM 67 (1979), Chapter VIII, §1, printed pages 127–129 (PDF pages
133–135). Source ID: `serre-1979-local-fields`; retained file
`C:/Central-Library/Serre--Local Fields--1979.pdf`; SHA256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.
Serre defines the degree-zero group as invariants modulo norms. Chapter VIII,
§3, Proposition 5, printed pages 131–132 (PDF pages 137–138), gives precisely
the degree-zero product normalization used here, including its extension along
an equivariant bilinear coefficient pairing. The comparison to Mathlib's
spliced chain/cochain complex and the quotient descent certificates are
internal formalization work.

Development status: this pair is being implemented and has not been
independently accepted or published. It constructs only the degree-zero
comparison and product. The all-degree maps, products, connecting signs,
and comparisons remain separate obligations of the task.
