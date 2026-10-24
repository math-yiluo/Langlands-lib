# Elementary edge cases for the tempered exponent criterion

The theorem `Langlands.glTemperedExponentEdge` proves the closed proposition
`Langlands.GLTemperedExponentEdgeStatement` from
`Langlands.Representation.Classification.TemperedExponentEdgeStatement`.
The field and complex carrier universes remain independent. The result bundles
the zero-carrier case in every rank and the unitary-central-character conclusion
for a nontrivial smooth representation in positive rank.

## Zero carriers

The private lemma `admissible_of_subsingleton` proves smoothness by using the
whole group as an open subgroup fixing each zero vector. Each fixed submodule
is subsingleton and hence finite as a complex module. The construction
`trivialCentralCharacter` supplies the trivial character of the full center;
its scalar action holds because all vectors are equal.

The lemma `tempered_of_subsingleton` shows that every descended coefficient norm
is the zero function by quotient induction, evaluation on a representative,
and the equality of every vector to zero. `MeasureTheory.MemLp.zero` then
supplies all the integrability assertions, for every measure required by the
actual analytic predicate.

The lemma `zeroCarrierClause` installs the topology and quotient measurable
structure supplied by the local field. The Jacquet quotient map is surjective,
so its target is subsingleton. A generalized eigencharacter would supply a
nonzero vector in that target, which is impossible.

## Nontrivial carriers and the scalar character

The general helper `scalarCharacter_open_kernel` uses a nonzero smooth vector
and an open subgroup fixing it. Under a continuous homomorphism into the
representation group, the inverse image of that subgroup is open. Scalar
cancellation shows that this inverse image lies in the character kernel.
An overgroup of an open subgroup is open.

For `scalarCharacter_unitary`, choose the single block of positive size `n`.
Its unipotent radical is subsingleton by
`GeneralLinear.BlockShape.subsingleton_unipotentRadical`. The identity linear
map descends through the Jacquet quotient and is a left inverse to its quotient
map. Thus a nonzero original vector remains nonzero. The block modulus is one,
since there are no strictly ordered pairs of block indices. The representative
formula `splitCentreJacquet_mk` and the given scalar action make this vector
an eigenvector for the character obtained by applying the supplied character
to the single coordinate. Its kernel is open by continuous evaluation.
The eigenvector therefore supplies an actual Jacquet exponent.

Every one-coordinate tuple satisfies the weak monotonicity condition.
Testing the assumed bound at a unit gives norm at most one; testing at its
inverse gives the reverse inequality. The supplied scalar character has norm
one at every unit.

## The full center

The lemma `unitaryCentralCharacterClause` first applies the open-kernel helper
to the continuous scalar homomorphism. It then identifies the full center with
field units: `GeneralLinear.scalarEmbedding` gives injectivity in positive
rank, and `Matrix.GeneralLinearGroup.center_eq_range_scalar` gives
surjectivity. The resulting algebraic multiplicative equivalence transports
the supplied character to the full center. Its scalar action and norm-one
property follow by writing a central element as a scalar.

The proof obtains openness of the transported character kernel by applying
`scalarCharacter_open_kernel` to the continuous inclusion of the center.
It does not require a continuity assertion for the inverse algebraic
equivalence. These fields form the actual `UnitaryCentralCharacter` datum.
The closing theorem combines the two clauses without additional hypotheses.

## Provenance and scope

This is an internal elementary deduction from the imported definitions and
proved algebraic and topological lemmas. The implemented proof follows the
reductions described in the statement's Markdown. Worker 19 contributed the
zero/nonzero-carrier distinction, and Worker 8 identified reusable one-block
and eigencharacter lemmas.

The theorem proves no coefficient growth estimate, Haar volume bound, or
equivalence between analytic temperedness and the general exponent condition.
Those are separate obligations of the full criterion.
