# The Hasse–Minkowski isometry theorem over number fields

Workers 787 and 864.

`Langlands.numberFieldQuadraticIsometry` proves the published
`Langlands.NumberFieldQuadraticIsometryStatement.{u}`. Over any number
field and in every dimension, including zero, suppose both forms have
nondegenerate polar bilinear forms. If their actual tensor scalar
extensions are isometric at every finite and archimedean completion,
the forms are isometric over the number field.

The proof composes the cyclic Hasse norm theorem, the quadratic isotropy
theorem obtained from it, and the reduction from isotropy to isometry.
The cyclic norm proof uses vanishing of the first cohomology of the
idele class group and the principal idele sequence. The quadratic
argument diagonalizes the forms, treats the binary and ternary cases
by square reflection and norm descent, and treats rank four by descent
from the discriminant extension. For higher ranks, weak approximation
and cofinite ternary isotropy reduce the rank one step at a time. The
isometry reduction transfers a common nonzero value and cancels the
line of that value over every completion. Induction gives the isometry
over the number field.

The target is the quadratic isometry assertion in Platonov–Rapinchuk,
*Algebraic Groups and Number Theory*, § 6.6, printed pp. 347–349. The
implemented argument follows the arithmetic approach in Voight,
*Quaternion Algebras*, Theorem 26.8.24 and Corollary 26.8.25, printed
p. 451.

The registered sources are `platonov-rapinchuk-1994-algebraic-groups-number-theory`
(SHA-256 `c333b953ca0ace6306663f648cd853a75da55023bf873e0ef2688d997216717f`)
and `voight-2021-quaternion-algebras`
(SHA-256 `f6c56f6ca7b4bee139b88865a3cf045f899da59d0217618c4dc81daf19ef1ad4`).

## Dependency check

The Lean type-and-value scan checked all three project exclusions and their
proof name prefixes. None occurs in the transitive closure of the theorem.
The target and its 43 project imports match the Library base byte for byte.
The cyclic norm proof uses the idele-level Galois product identity
extracted from the existing proof for idele classes, with the original
quotient result proved using that identity. [Lean dependency closure](NumberFieldQuadraticIsometryDependencies.md)
