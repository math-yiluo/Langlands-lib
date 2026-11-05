# Opposite Chevalley data

Module `Langlands.GroupScheme.SplitExistence.Opposite`, namespace
`Langlands.GroupScheme.SplitExistence` (the Chevalley-data part is in `ChevalleyData`).
Internal helper of the proof of the split reductive Existence Theorem (task 2132924b). The
statements about negating a root pairing are standard. The construction of opposite Chevalley
data is derived content: it lets every argument that uses the positive side `B = T·U⁺` also be
applied to the negative side `T·U⁻`.

## `SL₂` swap

- `swapMat`: the matrix `[[0, 1], [1, 0]]`. `swapMat_mul_self` says it squares to `1`, and
  `det_swapMat` says its determinant is `-1`.
- `sl2Swap`: conjugation by `swapMat`, a group endomorphism of `SL₂(R)` for every commutative
  ring `R`. `coe_sl2Swap` gives its matrix.
- `sl2Swap_upper`, `sl2Swap_lower`: it exchanges `[[1, s], [0, 1]]` and `[[1, 0], [s, 1]]`.
- `sl2Swap_diag`: it sends `diag(t, t⁻¹)` to `diag(t⁻¹, t)`.
- `sl2Swap_weyl`: it sends `[[0, 1], [-1, 0]]` to `[[0, 1], [-1, 0]] · diag(-1, -1)`.
- `sl2Swap_map`: it commutes with change of rings.

## Negating a root pairing

For a root pairing `P` over any commutative ring:

- `negIndex P`: the involution `i ↦ reflectionPerm i i` of the index type, which sends `α` to
  `-α`. `negIndex_negIndex` says it is an involution.
- `negEquiv P : RootPairing.Equiv P P`: the automorphism `-id` on weights and on coweights,
  with index map `negIndex P`.
- `negBase b`: the base `-b`, the image of `b` under `negEquiv`. `mem_negBase_support` says
  `i ∈ (-b).support ↔ reflectionPerm i i ∈ b.support`.
- `reflection_negIndex`, `reflectionPerm_negIndex`: the reflections of `-α` and of `α`
  coincide, as linear maps and as permutations of the index type.

## Opposite Chevalley data

For Chevalley data `D : ChevalleyData P b`:

- `negSimple i`: the simple root `α` of `b` attached to the simple root `-α` of `-b`, and
  `reflectionPerm_negSimple` recovers `i`.
- `signChar P R i`: the character `x ↦ (-1) ^ ⟨x, α_i^∨⟩` of `X` with values in `Rˣ`, and
  `φ_sl2Diag_neg_one`: `φ_i(diag(-1, -1))` is the torus element of `signChar`.
- `D.neg : ChevalleyData P (negBase b)`. It has the functional `-ℓ`, the same `n`, `wt`, root
  operators `e` and commutator data, and the `SL₂`-homomorphism `φ_{-α} := φ_α ∘ sl2Swap` for
  each simple root `-α` of `-b`. Proofs of the fields:
  - `ℓ_pos`: `-ℓ(-α) = ℓ(α) > 0`.
  - `φ_upper`, `φ_lower`: by `sl2Swap_upper` and `sl2Swap_lower`, the upper and lower root
    groups of `-α` are the lower and upper root groups of `α`.
  - `φ_diag`: by `sl2Swap_diag`, using that the coroot of `-α` is `-α^∨`.
  - `weyl_weight`: from `sl2Swap_weyl`, the Weyl element of `-α` is the Weyl element of `α`
    times a diagonal matrix. So its nonzero entries are among those of the Weyl element of `α`,
    and the reflections of `α` and `-α` agree (`reflection_negIndex`).
  - `weyl_conj`: conjugation by the Weyl element of `-α` is conjugation by that of `α` after
    conjugation by `signChar`. That conjugation rescales `x_j(s)` by `(-1)^⟨α_j, α^∨⟩`
    (`torusHom_conj_x`), so the sign `ε` is multiplied by `±1`.
