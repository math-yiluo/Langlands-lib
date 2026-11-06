# Finite matching from block multiplicities

These internal finite combinatorial constructions support
`Blocks.DecompositionUniqueness` and add no representation-theoretic hypotheses.
They apply over any field and group, with independent carrier universes and
independent finite index types.

`exists_equiv_of_fiber_card_eq` chooses a finite equivalence between each pair
of fibers with equal cardinality, and combines them using `Equiv.ofFiberEquiv`.
`exists_equiv_of_setoid_card_eq` applies this construction to the quotient maps
from the two families into a common quotient of their disjoint union.

`BlockDataMatch` means equal lengths and existence of an actual Weil-factor
intertwining equivalence. Its reflexivity, symmetry and transitivity use the
identity, inverse and composition of those equivalences. `blockIndexSetoid`
uses this relation on the tagged union of the two families; the tags let the
two carrier universes stay independent.

`matching_of_class_counts` needs equal multiplicities for every class occurring
in either family. Quotienting the tagged index set and matching its fibers
then gives the required bijection of summands, preserving lengths and Weil
factors. This is a derived finite combinatorial step; it does not itself prove
that isomorphic pairs have equal block multiplicities.
