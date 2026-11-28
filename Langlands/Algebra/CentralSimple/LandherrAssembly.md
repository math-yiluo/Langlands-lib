# Assembly lemmas: padded targets, scalar extension of products, coordinate approximation

Module: `Langlands.Algebra.CentralSimple.LandherrAssembly`.

- In `exists_target_nbhd`, `B` is finite-dimensional over `F` and `k` is a complete
  nontrivially normed field over `F` with `2 ≠ 0`. If a list `l` of entries satisfies
  `listProd l · D · ᵗτ_k(listProd l) = 1`, then for every
  length `L ≥ l.length` there are coordinates `c₀` and neighbourhoods `t α ∋ c₀ α` such that
  for all coordinates `c` in these neighbourhoods `targetMap D (coordPoint c)` is the square
  of an element of the `k`-subalgebra it generates. The list is padded with `(0, 0)` blocks
  to length `L` (`listProd_pad`, `ofFn_getD_eq`), and `exists_coord_nbhd` (module
  `Langlands.Algebra.CentralSimple.LandherrContinuity`) applies.
- `matrixBaseMap_matrix`: entrywise scalar extension `M₂(B) → M₂(k ⊗_F B)` commutes with the
  transposed involutions `ᵗτ` and `ᵗτ_k`.
- `matrixBaseMap_targetMap`: scalar extension sends `t D ᵗτ(t)`, with
  `t = listProd (List.ofFn g)` over `B`, to `targetMap (matrixBaseMap D)` of the entries
  `1 ⊗ g j` (by `map_listProd` and `matrixBaseMap_matrix`).
- `exists_approx_coords`: coordinatewise version of `exists_strongApprox` (module
  `Langlands.Algebra.CentralSimple.LandherrStrongApprox`): for a finite index type `κ`, given
  neighbourhoods at the finite places of `S` and at all infinite places for each coordinate,
  and `v₀ ∉ S`, there is `x : κ → F` meeting all of them and integral at every finite place
  outside `S ∪ {v₀}`.

## Provenance

Bookkeeping for the approximation argument in the proof of Landherr's theorem (module
`Langlands.Algebra.CentralSimple.LandherrMain`).
