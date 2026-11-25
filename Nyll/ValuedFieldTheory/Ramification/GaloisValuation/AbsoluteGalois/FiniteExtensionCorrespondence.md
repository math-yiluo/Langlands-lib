# Absolute Galois groups of finite extensions as open subgroups

Module `Nyll.ValuedFieldTheory.Ramification.GaloisValuation.AbsoluteGalois.FiniteExtensionCorrespondence`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a field, `K̄` its algebraic closure (`AlgebraicClosure K`), `G_K = Gal(K̄/K)`, and `i : L → K̄` a `K`-embedding of a finite extension `L`. The file identifies `G_L` with the open subgroup of `G_K` fixing `i(L)`, as topological groups, and records how this subgroup behaves under conjugating `i`, under towers and composita, and for normal `L / K`.

## Main definitions

- `fixingSubgroupOfExtension K i`: the elements of `G_K` fixing `i(L)` pointwise; no finiteness needed. For finite `L`, `openSubgroupOfFiniteExtension K i` is the same subgroup as an open subgroup.
- `openSubgroupOfNormalClosureFiniteExtension K i`: the normal open subgroup fixing the normal closure of `i(L)`; the quotient by it is the Galois group of that normal closure.
- `conjugateEmbedding K i σ = σ ∘ i`; `openSubgroupOfFiniteExtensionSup`: the subgroup attached to the compositum of two embedded extensions, i.e. the intersection.
- `equivGalFieldRangeOfFiniteExtension K i : G_L ≃* Gal(K̄ / i(L))`, and its topological version.
- `equivOpenSubgroupOfFiniteExtension(ContinuousMulEquiv)`: `G_L` is isomorphic to the open subgroup.
- `ofFiniteExtensionAbsolute K i : G_L →* G_K`: the resulting inclusion.
- `ofFiniteExtensionAbsoluteTower K i j : G_M →* G_L` for `L → M → K̄`.

## Main results

- `isOpen_fixingSubgroupOfExtension`, finite index instances; `openSubgroupOfFiniteExtension_index_eq_finrank`: the index is `[L : K]`, assuming `K̄ / K` Galois.
- `openSubgroupOfFiniteExtension_conjugateEmbedding_eq_map`: conjugating `i` by `σ` conjugates the subgroup by `σ`.
- Larger embedded fields give smaller subgroups.
- For `L / K` normal: the subgroup is normal and `G_K / G_L ≃* Gal(L/K)` (`quotientOpenSubgroupEquivGalOfNormalFiniteExtension`, `quotientRangeEquivGalOfNormalFiniteExtension`, and versions with `Gal(i(L)/K)`).
- `ofFiniteExtensionAbsolute_isOpenEmbedding`, `range_ofFiniteExtensionAbsolute`: `G_L → G_K` is injective, continuous, an open embedding, with image the subgroup fixing `i(L)`.
- `ofFiniteExtensionAbsoluteTower_naturality`, `…_injective`, `map_top_ofFiniteExtensionAbsoluteTower_eq_comap_range`: the tower map is compatible with the inclusions, injective, and its image is the preimage of the image of `G_M`.
- `HenselianDVF.mem_absoluteValuationSubring_iff_apply_mem_of_finite_separable_intermediate`: for a `HenselianDVF` structure `F` on `K` and a valuation ring `A` of `K̄` whose valuation extends that of `F`, `G_K` preserves membership in `A` on a finite separable level `E`, given a `HenselianDVF` structure on `E` with valuation ring `A ∩ E` and the unique-extension property over `F`.

## Watch for

- The index formula takes `IsGalois K (AlgebraicClosure K)` as a hypothesis, which fails for imperfect `K`; without it only the normal-closure subgroup gets an index formula (`openSubgroupOfNormalClosureFiniteExtension_index_eq_galoisCard`).
- `G_L ≃ Gal(K̄ / i(L))` depends on a chosen isomorphism of algebraic closures (`IsAlgClosure.equiv`), so `ofFiniteExtensionAbsolute` is canonical only up to that choice; its image does not depend on it.
- The last result assumes the finite-level uniqueness of the valuation ring rather than proving it.
- Apart from the last result, the declarations live in the namespace `RamificationTheory.Field.absoluteGaloisGroup`, not in Mathlib's `Field.absoluteGaloisGroup`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/GaloisValuation/AbsoluteGalois/FiniteExtensionCorrespondence.lean`: the Lean file is the source byte for byte (SHA-256 `c80c817abda86b609af026f6f71c3c7721a53a58374737bc8a2b661c2db38985`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
