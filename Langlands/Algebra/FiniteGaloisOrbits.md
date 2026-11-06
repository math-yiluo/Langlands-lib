# Finite Galois sets and stabilizer fixed fields

This internal construction uses Mathlib's finite Galois correspondence,
extension of embeddings to a normal field, and orbit–stabilizer equivalence.
For a finite Galois extension `L/k`, restriction of automorphisms to the fixed
field of a subgroup identifies its left cosets with the field's `k`-embeddings
in `L`. The equality criterion uses `fixingSubgroup_fixedField`.

For any action of `Gal(L/k)` on a type `I`, the field `stabilizerField i` is the
fixed field of the point stabilizer. The orbit of `i` is equivalent to the
embeddings of that field. The inverse equivalence intertwines postcomposition
of embeddings and the original group action.

Choosing one representative per orbit gives `orbitField` and
`sigmaEmbeddingEquiv`. This identifies the dependent union of all embeddings of
these orbit fields with `I`, equivariantly. No finiteness or nonemptiness of `I`
is required for these constructions; an empty `I` has no orbit fields.

For a finite `I : Type u`, `exists_finite_fields` reindexes the orbit fields by
`Fin n`. It returns those fields and an equivalence
`(Σ i : Fin n, E i →ₐ[k] L) ≃ I`, together with its postcomposition equivariance.
This includes `n = 0` when `I` is empty. The coefficient fields retain the
arbitrary universe `u`; no characteristic assumption is used.
