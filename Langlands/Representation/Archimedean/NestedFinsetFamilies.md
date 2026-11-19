# Uniqueness of a nested finite family

`Langlands.Archimedean.eq_antitone_of_card_of_occurrences` is a double-counting
lemma for the real compact multiplicity calculation. It is derived directly
from finite-set cardinality and finite sums.

For each target set, intersect every member of each family with that set.
Nestedness makes the size of each target intersection the smaller of the two
target cardinalities. The corresponding intersection for the other family
cannot exceed that size. The total sizes agree by summing the occurrence counts
over elements of the fixed target set. Hence equality holds at each index.
In particular the fixed target set is contained in the set with the same index
in the other family, and their equal cardinalities give equality.
