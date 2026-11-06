# Reindexing finite direct sums of Weil–Deligne pairs

`WeilDeligneRepresentation.directSumReindexEquiv e X` is the pair equivalence
`⊕_{j : κ} X j ≃ ⊕_{i : ι} X (e i)` for an equivalence `e : ι ≃ κ` of finite
index types. Its linear map is Mathlib's `DirectSum.lequivCongrLeft K e.symm`:
the coordinate at index `i` on the right is the coordinate at `e i` on the left.
That map commutes with the Weil-group action and with the monodromy coordinatewise.
Both equalities are checked by `LinearMap.ext` and `DirectSum.ext` and hold by
definition.

This internal construction is shared by the correspondence assembly. Its field, group, carrier and two index universes are independent; both index types are finite. It reuses the existing direct-sum pairs and changes only their indexing.
