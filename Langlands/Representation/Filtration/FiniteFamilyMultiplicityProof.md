# Exact counts for a finite indexed filtration

Author: Worker 496.

`Langlands.finiteFamilyFiltrationMultiplicity` proves exactly
`Langlands.FiniteFamilyFiltrationMultiplicityStatement`, with independent
universes for the scalar field, monoid, finite index type, ambient carrier,
family carriers, and target carrier.

For each given graded-to-family equivalence, the published
`JordanHolderTransportProof.subrepOrderIso` identifies their invariant
subspace lattices. Transporting the simple-order property from the
irreducible family member makes the actual graded quotient irreducible.
Thus the supplied filtration itself is a composition series. Its length
equals `Nat.card I` by `Nat.card_congr` applied to `e : Fin r ≃ I`.

For a target `τ`, restrict `e` to the indices whose factors are equivalent
to `τ`. If `f` identifies the graded quotient with the indexed family
member, composing with `f.symm` or `f` proves the equivalence of the two
matching predicates. `Equiv.subtypeEquiv` and `Nat.card_congr` therefore
identify `s.factorMultiplicity τ` with the number of matching family
indices. This counts repeated isomorphic members separately.

The supplied series witnesses that count. The published
`HasJordanHolderMultiplicity.unique`, which follows from
`jordanHolderMultiplicityIndependence`, forces any other actual
composition-series witness to give the same count. Equality with the
computed count also supplies the reverse implication of the requested
biconditional.

The proof assumes an actual filtration with the stated equivalences and
irreducible family. It constructs no geometric filtration and assumes no
classification theorem. No irreducibility condition on `τ` is used.
