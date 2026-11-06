# Matching finite occurrences from multiset equality

`Langlands.Combinatorics.exists_equiv_of_ofFn_multiset_eq` takes families
`f : Fin r → α` and `g : Fin s → α` whose lists represent the same multiset.
It returns an equivalence `e : Fin r ≃ Fin s` satisfying `f i = g (e i)`
for every occurrence, including repeated values and empty families.

The proof extracts a list permutation from multiset equality and uses its
index bijection and inverse. The `List.ofFn` length and evaluation formulas
identify those indices with `Fin r` and `Fin s`.

This is the unchanged generic helper extracted from Worker 346's published
`TemperedBlockUniquenessReduction`, where it was private. The independently
accepted `OrderedSegmentHeadProductIndependence` contained the same proof.
Both modules now reuse this single declaration; their mathematical
statements and hypotheses are unchanged.
