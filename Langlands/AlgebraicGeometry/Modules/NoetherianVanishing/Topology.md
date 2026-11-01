# An irreducible piece of a closed subset of a noetherian space

Author: Worker 921.

This helper module is part of the proof of
`Langlands.AlgebraicGeometry.Modules.NoetherianSeparatedQuasicoherentVanishingStatement`. It
contains the point-set topology used by the vanishing induction. It does not mention schemes.

## Declarations

Namespace `Langlands.AlgebraicGeometry.Modules.NoetherianVanishing`, for a topological space
`X`.

- `exists_irreducibleCloseds_inter_subset [NoetherianSpace X] (Z : Closeds X)
  (hZ : (Z : Set X).Nonempty)`: there are an irreducible closed set `T` and an open set `O`
  with `T ⊆ Z`, `O ∩ Z` nonempty and `O ∩ Z ⊆ T`.
- `height_add_one_le_of_subset`: if `T' ⊆ T` are irreducible closed sets and some `x ∈ T`
  is not in `T'`, then `height T' + 1 ≤ height T`. Here `height` is Mathlib's `Order.height`
  in the poset `IrreducibleCloseds X`, valued in `ℕ∞`.
- `height_le_of_topologicalKrullDim_le`: if `topologicalKrullDim X ≤ d`, every irreducible
  closed set has height at most `d`.

## Proofs

- For the first statement, Mathlib's `NoetherianSpace.exists_finset_irreducible` writes `Z`
  as the supremum of a finite set of irreducible closed sets. The proof chooses such a set `S`
  of minimal cardinality (`Nat.find`). It is nonempty because `Z` is. For `T₀ ∈ S`, let `W`
  be the supremum of the other members. If `T₀ ⊆ W`, then `S` minus `T₀` would also represent
  `Z` with fewer members, so some `η ∈ T₀` lies outside `W`. Take `T = T₀` and `O` the
  complement of `W`: `η ∈ O ∩ Z`, and `O ∩ Z ⊆ T₀` because `Z = T₀ ∪ W`.
- The second statement is Mathlib's `Order.height_add_one_le` applied to `T' < T`.
- The third statement is `Order.height_le_krullDim`, since `topologicalKrullDim X` is by
  definition the Krull dimension of `IrreducibleCloseds X`.

## Provenance

Internal infrastructure. The first statement is the usual choice of an irreducible component of
`Z` together with an open set meeting `Z` only in that component (compare Mathlib's
`NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent`, Stacks Tag 0052, stated
there for the whole space). Height in the poset of irreducible closed subsets measures
dimension: the supremum of the heights is `topologicalKrullDim X`.
