# The split pinning of type `G₂` of the split Cayley automorphism group scheme

Notation as in `Torus.md`. For a field `K`, `Aut_K` is the automorphism group scheme of Zorn's
split Cayley algebra over `K`. `𝕋` is the rank-two split torus with coordinates `(s, t)`, and
`torusMap K : 𝕋 → Aut_K` is its closed embedding. Characters and cocharacters of `𝕋` are
identified with `ℤ²` by the published `GeneralLinear.characterCoordEquiv` and
`GeneralLinear.cocharacterCoordEquiv`. In these coordinates the pairing is the dot product
(`GeneralLinear.latticePairing_coord`). The twelve roots of `𝕋` are the characters
`rootChar K α` with coordinates `rootWeight α` (`roots_torusMap`, `Torus.lean`).

## Roots and coroots of any root datum of the torus

Let `P` be a root datum with `IsRootDatumOf (torusMap K) P`, so its pairing is the lattice
pairing and its roots are the roots of `torusMap K`.

- `exists_root_eq_rootChar`, `exists_index_eq_rootChar`: every root of `P` is some
  `rootChar K α`, and every `rootChar K α` is a root of `P`.
- `pairing_eq_coord`: if the root `j` of `P` is `rootChar K α`, then `P.pairing j j'` is the dot
  product of `rootWeight α` with the coordinates of the coroot `j'`.
- `exists_reflection_coord`: reflecting the root `β` in the root `α` gives a root `ξ`, with
  `rootWeight ξ = rootWeight β - ⟨β, α^∨⟩ rootWeight α`.
- `corootCoord_u1`: the coroot of the short root `u₁ = (1, 0)` has coordinates `(2, -1)`.
  Write `ν` for its coordinates. Then `⟨u₁, u₁^∨⟩ = 2` gives `ν₀ = 2`. Reflecting
  `l₂₃ = (1, 2)` in `u₁` gives the root `(-1 - 2ν₁, 2)`. The only root with second coordinate
  `2` is `l₂₃`, so `ν₁ = -1`. The Lean proof checks the twelve possible roots with `omega`.
- `corootCoord_l21`: the coroot of the long root `l₂₁ = (-1, 1)` has coordinates `(-1, 1)`. Write
  `ν` for its coordinates. Then `⟨l₂₁, l₂₁^∨⟩ = 2` gives `ν₁ = ν₀ + 2`. Reflecting `l₁₃ = (2, 1)`
  in `l₂₁` gives the root `(4 + 3ν₀, -1 - 3ν₀)`. Its coordinates sum to `3`, so it is `l₁₃` or
  `l₂₃ = (1, 2)`. The first case has no integer solution, and the second gives `ν₀ = -1`.
- `corootSpan_eq_top`: the coroots span the cocharacter lattice. The coroots `(2, -1)` and
  `(-1, 1)` give `(1, 0) = (2, -1) + (-1, 1)` and `(0, 1) = (2, -1) + 2 · (-1, 1)`.

## The base

- `regularCochar K`: the cocharacter with coordinates `(1, 2)`. `rootHeight α` is the pairing
  of `rootWeight α` with it, and `root'_regularCochar` identifies `P.root' j (regularCochar K)`
  with it. No root has height `0` (`rootHeight_ne_zero`), so `regularCochar K` is regular.
  The positive roots and their heights are `u₁ : 1`, `l₂₁ : 1`, `u₂ : 2`, `v₃ : 3`, `l₁₃ : 4`,
  `l₂₃ : 5`.
- `not_mem_baseOf_of_eq_add`: a root whose weight is the sum of the weights of two positive
  roots is not an indecomposable positive root.
- `mem_baseOf_iff`: the indecomposable positive roots for `regularCochar K` (Mathlib's `baseOf`)
  are exactly `u₁` and `l₂₁`. The other positive roots decompose as `u₂ = u₁ + l₂₁`,
  `v₃ = u₁ + u₂`, `l₁₃ = u₁ + v₃` and `l₂₃ = l₂₁ + l₁₃`. Conversely a root of height `1` is
  not a sum of two roots of positive height.

## The pinning

- `exists_coordinateRootDatum K`: `𝕋` has a reduced root datum `P` (the published
  `rootDatumExistence`), using that `Aut_K` is connected reductive (`isConnectedReductive`,
  `Radical.lean`), that `𝕋` is split, and that `torusMap K` is a maximal torus
  (`isMaximalTorus_torusMap`, `Torus.lean`, with connectedness from
  `connectedSpace_automorphismGroup`). The published
  `RootDatumCoweightFace.exists_base_support` gives a base `B` whose support is the set of
  indecomposable positive roots for `regularCochar K`, that is, `u₁` and `l₂₁`. Number them
  `l₂₁ ↦ 0` and `u₁ ↦ 1`. By `pairing_eq_coord` and the coroot coordinates,
  `⟨l₂₁, l₂₁^∨⟩ = 2`, `⟨l₂₁, u₁^∨⟩ = -3`, `⟨u₁, l₂₁^∨⟩ = -1` and `⟨u₁, u₁^∨⟩ = 2`. This is
  Mathlib's `CartanMatrix.G₂ = !![2, -3; -1, 2]`. The coroots span by `corootSpan_eq_top`.
- `exists_splitPinning K`: the split pinning of `Aut_K` with torus `𝕋`, inclusion
  `torusMap K`, root datum `P` and base `B`. The simple-root Lie trivializations come from the
  published `RootPinning.ofSplitMaximalTorus`. The construction follows the published
  `SymplecticMatrix.TypeCPinning.exists_splitPinning`.
- `splitCayleyAutomorphismPinning : SplitCayleyAutomorphismPinningStatement`: for every field
  `K`, combine the trivial centre (`center_eq_bot`, `Center.lean`) with
  `exists_splitPinning K`.
