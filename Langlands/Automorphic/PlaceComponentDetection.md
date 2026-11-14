# Detecting stable subspaces by a compact type

Module `Langlands.Automorphic.PlaceComponentDetection`, namespace
`Langlands.Automorphic.PlaceComponent`. Worker 174 wrote it as a step towards
`Langlands.Automorphic.CuspidalArchimedeanIrreducibleAdmissibleComponentStatement` (G1, Task 5992,
`8a7f44bc-c7bc-4ceb-96aa-6eff19b38f97`). Provenance: internal; elementary representation
theory of compact groups built on `Langlands.Representation.CompactMaschke`.

Setting: `κ` is a representation of a compact group `K` and `π` a Lie action on a complex
vector space `V`. A matrix representation `τ` of `K` is fixed. A stable subspace is
*`τ`-free* if it has no nonzero `τ`-intertwiner.

## Definitions

- `IsLocallyFinite κ`: every vector lies in a finite-dimensional `K`-stable subspace.
- `IsWeaklyContinuous κ`: `k ↦ μ (κ k x)` is continuous for every linear form `μ` and every
  `x`, as in the Library's `(𝔤, K)`-module predicates.
- `restrictRep κ W hW`: the restriction of `κ` to a `K`-stable subspace (Mathlib's
  `Subrepresentation.toRepresentation`).
- `hull κ π x`: the smallest stable subspace containing `x`.
- `freeSet π hfin hweak τ`: the vectors `x` whose hull is `τ`-free. It is a subspace.
  - `0` has hull `⊥`.
  - The hull of `x + y` lies in `hull x ⊔ hull y`.
  - The hull of `c • x` lies in `hull x`.

All definitions are internal to this proof.

## Results

- `isLocallyFinite_restrict` and `isWeaklyContinuous_restrict`: both properties pass to
  stable subspaces. Linear forms on a subspace extend (`LinearMap.exists_extend`).
- `intertwiners_bot`, `free_mono`: `⊥` is `τ`-free, and `τ`-freeness passes to subspaces.
- `eq_zero_of_free`: an intertwiner into the restriction to a `τ`-free subspace is zero.
- `free_map`: if `A` commutes with `κ` and `W` is `K`-stable and `τ`-free, then `A(W)` is
  `τ`-free. An intertwiner into `A(W)` lifts through `A|_W`
  (`CompactMaschke.exists_lift_intertwiner`), and the lift is zero.
- `free_sup`: a sum of two `K`-stable `τ`-free subspaces is `τ`-free. Lift through the
  addition map from the product representation `W₁ × W₂` (Mathlib's `Representation.prod`).
  Both components of the lift are zero.
- `hull_isStable`, `mem_hull`, `hull_le`, `isStable_sup`: basic facts on hulls.
- `freeSet_compact`, `freeSet_lie`: `κ k` and `π X` preserve the free set, because the hull
  of `κ k x` or `π X x` lies in the hull of `x`.
- `freeSet_map`: an operator `A` commuting with `κ` and `π` preserves the free set. The hull
  of `A x` lies in `A(hull x)`, which is stable; apply `free_map`.
- `exists_not_mem_freeSet`: a nonzero `x₀` is not free for some continuous matrix
  representation `τ`.
  - Take a finite-dimensional `K`-stable `E₀` containing `x₀` inside its hull, and a basis.
  - `τ` is the matrix of `κ` on `E₀` (`LinearMap.toMatrixAlgEquiv`). It is continuous, since
    its entries are coordinate forms of orbit maps.
  - The basis isomorphism `ℂ^d → E₀ ⊆ V` is a nonzero intertwiner into the hull
    (`LinearMap.toMatrix_mulVec_repr`).
- `intertwiners_ne_bot_of_freeSet_eq_bot` (**detection**): if the free set is zero, every
  nonzero stable subspace has a nonzero `τ`-intertwiner.
