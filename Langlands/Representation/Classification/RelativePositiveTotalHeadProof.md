# Actual GL heads from equal positive relative Jacquet counts

`Langlands.glRelativePositiveTotalHead` proves the exact published
`Langlands.GLRelativePositiveTotalHeadStatement`, with independent universes
for the field, test representation and inducing representation.

The composed normalized opposite Jacquet quotient defines an additive functor
from actual smooth ambient representations to algebraic refined-Levi
representations. Its maps preserve surjections by right exactness of
coinvariants. Additivity follows on actual quotient representatives.

The inducing representation is nonzero by irreducibility. Surjective
evaluation at the identity makes the actual outer induction nonzero, and the
assumed finite length supplies an actual smooth irreducible quotient.

For any such quotient, admissibility descends from normalized induction.
The compact-open cofinality needed for this descent follows from block
Iwahori factorization. Actual second adjointness turns the nonzero quotient
map into a nonzero map from the inducing irreducible representation to the
quotient's coarse opposite Jacquet module. This map is injective. Refined
opposite Jacquet exactness preserves that injection; actual normalized
transitivity then embeds the inner Jacquet module into the composed
opposite Jacquet module of the quotient.

The mapped quotient is surjective. Short-exact decomposition of its kernel
sequence gives an actual finite composition series and a count `c` in its
target. Injective count monotonicity gives `m ≤ c`. The published
`Classification.positiveTotalHeadCore` applies with the given positive
ambient total `m`. It proves existence and equality of all irreducible
quotient kernels, including quotients with isomorphic targets.

This is an internal derivation from published Library results. Outer finite
length and the two equal positive actual-series counts remain explicit
hypotheses. This proof does not supply them for generic inducing data.
