# Composition length of an actual glued functor

This internal algebraic module evaluates an existing `IsGluedFrom` witness
and computes the actual composition length of its value. It does not construct
a geometric-lemma filtration.

`GluedLengthFormulaStatement` records this equality for a supplied family of
pieces and a supplied gluing. `gluedLengthFormula` proves it in this module.

`IsGluedFrom.repLength_eq_sum` applies the published object-filtration length
formula to `RepFunctorFiltration.atObject`. The actual natural isomorphisms
from the graded quotients to the supplied pieces identify their lengths.
The permutation in `IsGluedFrom` disappears because a finite sum is invariant
under reindexing by an equivalence. The equality holds in `ℕ∞`, including
infinite lengths.

`repLength_eq_sum_on` discards pieces whose carriers are subsingletons outside
a supplied finite set. `repLength_le_card` bounds the length by that set's
cardinality if every retained piece has length at most one.
`repLength_eq_card` gives equality if every retained piece is irreducible.
The indices are counted with multiplicity: two isomorphic pieces at distinct
indices each contribute one.

No finite-length premise on the original object is used. The ground field,
group, carrier, source-object and source-morphism universes remain independent.
These are derived algebraic consequences of the published actual-filtration
and representation-length constructions, rather than new source assertions.
