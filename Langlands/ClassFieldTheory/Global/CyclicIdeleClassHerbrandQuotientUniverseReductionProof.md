# Proof of the idele-class Herbrand universe reduction

The theorem `cyclicIdeleClassHerbrandQuotientUniverseReduction` proves
`CyclicIdeleClassHerbrandQuotientUniverseReduction.{u, v}` by assuming the
common-universe assertion and transporting its conclusion to the original
independent-universe fields. It does not prove the arithmetic assertion
used as the premise.

For `F : Type u` and `E : Type v`, put
`F₀ = (⊥ : IntermediateField F E)`. This is a number field in `Type v`.
Mathlib supplies its number-field and Galois instances.
`baseImageAutEquiv F E` transports cyclicity from `Aut_F(E)` to
`Aut_F₀(E)`, so the premise applies to `F₀` and `E`.

The proof turns the degree-one and degree-two instances of
`relativeIdeleClassCohomologyBaseImageIso` into equivalences of their
underlying types. `Finite.of_equiv` transports the two finiteness
conclusions back to the original cohomology groups. `Nat.card_congr`
transports their cardinalities, and
`IntermediateField.finrank_bot'` identifies the extension degrees.
These equalities rewrite the cardinality formula from the premise into
the required formula over `F`. No nontrivial-degree assumption is used.

This is an internal transport argument using the existing arithmetic
idele-class action and Mathlib's intermediate-field and cardinality
APIs. The underlying field `E` and its actual idele-class coefficient
group stay unchanged.
