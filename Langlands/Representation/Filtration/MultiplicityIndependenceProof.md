# Independence of a single Jordan–Hölder multiplicity

Author: Worker 430.

`Langlands.jordanHolderMultiplicityIndependence` proves the exact published
`Langlands.JordanHolderMultiplicityIndependenceStatement` from
`Langlands.Representation.Filtration.MultiplicityStatement`. The field,
monoid, ambient representation carrier and counted representation carrier
have four independent universes. The result applies to any field and monoid.
Neither the counted representation's irreducibility nor the existence of
composition series for arbitrary representations is assumed.

## Implemented proof

The published `Langlands.jordanHolderSeriesComparison` supplies a bijection
`e : Fin n ≃ Fin m` between the indices of the two supplied actual composition
series. For each `i`, it also supplies an actual representation equivalence
`f` between their graded factors at `i` and `e i`.

The predicate defining `factorMultiplicity` is the existence of an equivalence
from that graded factor to the fixed representation `τ`. Composing with
`f.symm` takes such an equivalence on the first series to one on the second;
composing with `f` gives the reverse implication. `Equiv.subtypeEquiv`
therefore restricts `e` to a bijection between the two subtypes of counted
indices. `Nat.card_congr` equates their cardinalities, which are precisely the
two multiplicities. Repeated isomorphic factors are counted separately because
the construction is a bijection of indices. Empty series are included.

The helper `Langlands.HasJordanHolderMultiplicity.unique` unpacks the two
existential composition-series witnesses, applies the proved independence
theorem, and substitutes the witnesses' equalities to conclude that their
claimed multiplicities are equal.

## Provenance and scope

This is a derived cardinality consequence of the Library's published actual
Jordan–Hölder comparison. Its proof uses the imported comparison theorem and
Mathlib's subtype-equivalence and finite-cardinality constructions. It adds
no representation-theoretic assumption or external mathematical theorem.
The source motivation for multiplicities in Silberger §1 and BZ77 §1.2 is
recorded in the imported `MultiplicityStatement.md`; the implemented proof
does not depend on a further assertion from either source.

This pair establishes independence and uniqueness only. It supplies no
additivity theorem, existence of a composition series, Jacquet-functor result,
or relative recovery theorem.
