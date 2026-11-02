# Actual algebraic characters and norm-one adelic points

Let `F` be an arbitrary number field and `G` an actual group scheme over
`Spec F`. `AlgebraicCharacter F G` is the type of actual group-scheme
morphisms from `G` to the existing multiplicative group scheme over `F`.
It imposes no commutativity assumption on `G`.

`characterUnits` evaluates such a character on the actual scheme points over
a coefficient algebra, then applies the published multiplicative comparison
with coefficient units. Its coefficient naturality follows from the
naturality of the actual point functor and of that units comparison.
`continuous_characterUnits` composes the continuity of the target scheme map
with the regular-function proof of continuity into the units topology.
Specializing to the actual adele algebra gives `character`, a continuous
homomorphism to the existing full idele group.

`character_rational` proves that a principal rational point evaluates to a
principal idele, using exactly the diagonal adele algebra map.
`characterNorm` composes this evaluation with the existing normalized
`IdeleAbsoluteValue.full`. Thus `characterNorm_rational` follows from the
published normalized product formula `full_diagonalUnits`, with its finite
completion norms and archimedean real/complex multiplicities.

`normOneSubgroup` is the intersection of the kernels of these actual
character norms. Its membership formula quantifies over every `F`-rational
algebraic character. It is normal because every kernel is normal and closed
because every norm character is continuous and the unit value is closed.
`rationalSubgroup_le_normOneSubgroup` proves principal inclusion, and
`rationalNormOne` is the resulting actual principal map into this subgroup.
For affine `G`, the subgroup inherits the Hausdorff topological group
structure. If the structural morphism is locally of finite type, it is
locally compact because it is closed in the actual locally compact adelic
point group.

This implements Getz–Hahn, *An Introduction to Automorphic Representations*
(2024), Section 2.6, equation (2.19) and the principal-inclusion sentence
immediately after it, printed page 68. The book writes the norm target as
positive reals; here it is the existing `ℝ≥0ˣ` realization of strictly
positive real numbers. The topology, normality and local compactness are
internal consequences of the constructed maps and existing coefficient-point
topology. The October 2026 errata contain no correction to this passage.

Rational injectivity, discreteness and closedness, the split-centre subgroup
in (2.20), its quotient and the homeomorphism (2.22), unimodularity, quotient
measure, reduction theory and finite volume remain separate obligations.
