# Actual one-factor series and multiplicities of an irreducible object

`Langlands.irreducibleMultiplicity` proves the exact proposition
`Langlands.IrreducibleMultiplicityStatement`. Its two component proofs are
`IrreducibleMultiplicityProof.compositionSeries` and
`IrreducibleMultiplicityProof.multiplicity`. The coefficient field, acting
monoid, ambient carrier and specified constituent carrier retain independent
universes `uK`, `uG`, `uA` and `uT`.

## The actual graded quotient

The proof reuses `LengthTwo.oneStep A.ρ`, the published invariant chain
consisting of zero and the whole representation. The helper
`oneStepGradedEquiv` constructs the actual equivalence from its unique graded
quotient to `A.ρ`.

First send an ambient vector to the corresponding vector in the top
subrepresentation, and then to its class modulo the pullback of the zero
subspace. This composite linear map is equivariant by the definitions of the
subrepresentation and quotient actions. Equality of two image classes says
that their difference lies in the zero subspace, which proves injectivity.
Every quotient class has a representative in the top subrepresentation;
its underlying ambient vector maps to that class, which proves surjectivity.
The resulting bijective intertwiner gives a representation equivalence.
Taking its inverse gives the asserted graded-to-ambient orientation.

For irreducible `A.ρ`, bottom is covered by top in its subrepresentation
lattice. The existing `LengthTwo.oneStep_hasSimpleFactors` then proves that
the actual one-step chain has simple factors. Together with the constructed
equivalence, this proves the first clause. No numerical length equality is
used to replace the required filtration witness.

## Counting the only factor

`oneStep_factorMultiplicity` proves the one and zero conditional count
formulas directly from the definition of `factorMultiplicity` as `Nat.card`
of a subtype of `Fin 1`.

For its sole possible index, compose a factor equivalence with the inverse
of `oneStepGradedEquiv` to obtain an equivalence from `A.ρ` to `τ.ρ`.
Conversely, compose an equivalence from `A.ρ` to `τ.ρ` with
`oneStepGradedEquiv` to obtain the required factor equivalence. Thus the
matching-index subtype is inhabited precisely when `A.ρ` and `τ.ρ` are
equivalent. In the inhabited case it is a subsingleton subtype of `Fin 1`,
so `Nat.card_unique` gives count one. In the other case it is empty, so
`Nat.card_of_isEmpty` gives count zero. No irreducibility of `τ` is used.

## Every actual composition series

The proof of `multiplicity` splits according to existence of an equivalence
between `A.ρ` and `τ.ρ`. In each case the same actual one-step chain, its
simple-factor proof and the computed factor count construct a genuine
`HasJordanHolderMultiplicity` witness, of count one or zero respectively.

For any other supplied multiplicity witness of count `m`, the published
`HasJordanHolderMultiplicity.unique` compares its actual series with the
constructed one-step series, yielding `m = 1` or `m = 0`. That uniqueness
result uses the published Jordan–Hölder series comparison and selected-factor
counting. Conversely, either equality transports the constructed witness to
count `m`. Simplification of the equivalence split gives exactly the
statement's disjunction. This proves both existence and exclusion of every
other count; the argument cannot become vacuous through missing series.
The final theorem pairs the two component proofs in the statement's order.

## Provenance and scope

This is an internal algebraic derivation from the published actual filtration
and multiplicity definitions, `LengthTwo.oneStep` and its simple-factor
criterion, quotient operations, and multiplicity independence. It is not
attributed as a literal theorem from the representation-theoretic literature.
It applies to arbitrary fields and monoids and adds no finite-dimensionality,
group-inverse, smoothness, admissibility or rank hypothesis.

The proof imports no multiplicity-additivity theorem. It supplies no
normalized induction or Jacquet comparison, support map, second adjointness,
continuation argument, relative recovery or Langlands classification theorem.
Those remain separate prerequisites and downstream obligations.
