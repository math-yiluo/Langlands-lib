# Detecting a full-center exponent from one central operator

Author: Worker 19.

`Langlands.CentralEigenvalueDetectionStatement.{uG,uV}` is a closed
proposition with independent universes for the group and representation
carrier. The group is a topological group. The representation is a
complex representation satisfying the project's `IsAdmissible`: every
vector is fixed by an open subgroup, and every open subgroup has a
finite-dimensional space of fixed vectors.

For any element `z` of the full group center, complex number `μ`, natural
number `n`, and nonzero vector `v` killed by `(ρ z - μ) ^ n`, the statement
asserts the existence of a character `χ` of the full center whose kernel is
open, whose uniform generalized central-character space is nonzero, and
whose value at `z` is `μ`. These first two conditions are precisely
`Langlands.IsCentralExponent ρ χ`. In particular, ordinary eigenvalues are
covered by exponent `n = 1`.

This is a derived internal linear-algebra statement, extracted for the
general rational strict Jacquet square-integrability proof. Its intended
proof adapts the finite fixed-vector argument of the published
`Langlands.exists_eigencharacter_extension` to the generalized eigenspace
of a single operator. Admissibility makes the intersection of that
eigenspace with one open subgroup's fixed vectors finite-dimensional.
The commuting full-center operators have a common eigenvector there.
No global decomposition, finite length, irreducibility, Jacquet
admissibility, or coefficient estimate is asserted.
