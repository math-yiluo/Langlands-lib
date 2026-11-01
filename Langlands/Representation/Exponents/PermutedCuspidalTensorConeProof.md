# Keeping original scalar witnesses through tensor permutations

This internal proof implements `Langlands.PermutedCuspidalTensorConeStatement`.
It retains the analytic square-integrability hypothesis and the supplied actual
Jacquet subquotient. The field and carrier universes are independent.

The helper `permutedCuspidalTensorScalar` forms the character on the permuted
block Levi by multiplying the original characters `c (e i)` on their respective
new coordinates. The elementary pure-tensor scalar-action lemma gives its
action on the actual block tensor. Multiplicativity of the complex norm and
the supplied individual norm formulas give its real part exactly `x ∘ e`.
The argument neither chooses new characters nor repeats real unitarization.

Every factor is nonzero by irreducibility. Choose a vector-space basis in each
factor and one index in each basis. The corresponding vector in the tensor
product basis is nonzero, so the actual external tensor is nonzero.
`squareIntegrableActualJacquetCone` now applies to the supplied subquotient,
the product scalar character, and that exact real part.

The proof does not construct the permutation or its actual occurrence. When
the original coordinates contain individual rank weights, composition with
`e` retains those weights, including repetitions and unequal block sizes.
Using this same original vector for two permutations permits the separate
finite-complement obstruction to compare complementary sums.

The representation-theoretic dependency is the actual scalar Jacquet cone
proof; its paired explanation records the local detector, Jacquet and analytic
strict-cone route. The extra scalar calculation is direct tensor multilinearity
and finite-product norms, and nonzeroness is elementary vector-space algebra.
No support classification or common-line conclusion enters the adapter.

The recursive project import audit contains 423 modules with no unresolved
imports or occurrence of any conclusion name excluded by the host task.
The adapter adds only the supplied-factor scalar calculation and elementary
tensor nonzeroness to the audited actual scalar Jacquet cone route.
The full host proof still requires its own audit after the occurrence,
grouping and integer-orbit constructions have been assembled.
