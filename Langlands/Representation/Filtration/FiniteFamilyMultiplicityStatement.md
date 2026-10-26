# Counting a finite family of composition factors

Author: Worker 496.

`Langlands.FiniteFamilyFiltrationMultiplicityStatement` is an internal
proposition interface for extracting exact length and multiplicity from a
supplied actual filtration. This file states the interface; it proves no
theorem.

Let `k` be a field, `G` a monoid, and `I` a finite type. Let `A` be a
representation and let `family : I → Rep k G` consist of irreducible
representations. Suppose an actual zero-to-full filtration `s` of `A` has
`r` graded quotients, an equivalence `e : Fin r ≃ I`, and an actual
representation equivalence between its quotient at `i` and `family (e i)`.
Then `A` has a composition series of length `Nat.card I`. For every
representation `τ` and every natural number `m`,

```
HasJordanHolderMultiplicity A τ m
  ↔ m = Nat.card {i : I // Nonempty ((family i).ρ.Equiv τ.ρ)}.
```

The subtype counts indices, so isomorphic family members contribute
separately. The target `τ` need not be irreducible: the supplied factors are
irreducible, and the equivalence predicate already determines whether any
of them can match `τ`. The scalar field, monoid, index type, ambient
representation, family carriers, and target carrier have independent
universes.

The premises supply an actual filtration and actual graded equivalences.
They assume neither a multiplicity formula nor independence of composition
series. The conclusion's biconditional requires both a series realizing the
specified count and exclusion of every other count.

This is an internal algebraic adapter derived from the Library definitions
`ObjectRepFiltration`, `HasCompositionSeriesLength`,
`ObjectRepFiltration.factorMultiplicity`, and
`HasJordanHolderMultiplicity`. Its intended proof transports irreducibility
across the given equivalences, counts matching indices by
`Equiv.subtypeEquiv` and `Nat.card_congr`, and uses the published
`jordanHolderMultiplicityIndependence` to compare all other series with the
supplied one. It asserts no geometric filtration or representation-theoretic
existence result beyond its input. No external literature translation is
claimed for this internal interface.
