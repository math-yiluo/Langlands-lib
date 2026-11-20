# Proof of the stable even-path geometry statement

Author: Worker 4348.

Lean module: `Langlands.LinearAlgebra.RootDatumEvenPathGeometryProof`. It proves
the published statement `Langlands.LinearAlgebra.EvenPathOrbitGeometryStatement`
(module `Langlands.LinearAlgebra.RootDatumEvenPathGeometryStatement`; Task 5736):

```lean
theorem Langlands.LinearAlgebra.evenPathOrbitGeometry :
    EvenPathOrbitGeometryStatement.{u, v, w, z}
```

Provenance: internal. The statement is an internal combinatorial prerequisite
of the even-chain Galois-data proof (Task 5375). Its Markdown and the Markdown of
the published helper module `RootDatumPairedPaths` give the source account
(Steinberg 1965, 9.4 and the notation before 9.11). This proof adds no new
mathematical claim beyond the statement. The closing theorem has no hypotheses
beyond those of the statement: an arbitrary group `Γ`, a finite root index type,
and `IsPairingCompatible b ρ`. Its axioms are `propext`, `Classical.choice` and
`Quot.sound`.

Almost all of the geometry is already in the published module
`Langlands.LinearAlgebra.RootDatumPairedPaths`. Its pair index type, paths,
action on pairs and level function are used unchanged. This module puts them into
the structures `EvenPathFamily`, `EvenPathFamily.CompatibleAction` and
`EvenPathFamily.OrbitOrdering` of `RootDatumEvenPathGeometry`. It also
constructs the ordering of the remaining roots. All declarations other than the
closing theorem are in the namespace
`Langlands.LinearAlgebra.RootDatumEvenPathGeometryProof`. Throughout,
`hρ : IsPairingCompatible b ρ`.

## The path family

- `J` is `RootDatumPairedPaths.PairIndex ρ`. A paired simple root `a` is one
  that some group element moves to a distinct simple root which is not orthogonal
  to `a`. `PairIndex ρ` has one element for each unordered pair `{a, partner a}`
  of a paired root and its partner. It is `Finite`, and the theorem uses
  `Fintype.ofFinite` for the required `Fintype J`.
- `pairFamily hρ : EvenPathFamily b (PairIndex ρ)` has `half := half hρ`,
  `path := path hρ`, `isPathComponent := isPathComponent_path hρ` and
  `disjoint := path_disjoint hρ`. All four are from `RootDatumPairedPaths`.
  Each path has even length `2 * half c`. Its middle pair is the pair `c`:
  `pairFamily_middleLeft` gives `middleLeft c = c.1` (from `path_left`), and
  `pairFamily_middleRight` gives `middleRight c = partner ρ c.1` (from `path_right`).
- `mem_rest_iff`: a simple root avoids every middle pair exactly when it is not
  paired. This uses `isPaired_iff_exists`, which says that `z` is paired iff it is
  `c.1` or `partner c.1` for some pair `c`. Consequently `not_isPaired_rest`:
  every element of `(pairFamily hρ).Rest` is unpaired.

## The compatible action

- `pairPerm hρ : Γ →* Equiv.Perm (PairIndex ρ)` is `MulAction.toPermHom` of the
  published action `pairAction hρ`. Its value on `c` is `pairSMul hρ γ c`
  (`pairPerm_apply`, by `rfl`).
- `isPathComponent_apply`: `ρ σ ∘ path c` is again a path component. This is
  `IsPathComponent.comp_perm` together with
  `IsPairingCompatible.pairing_apply`.
- `exists_shared`: by the published `exists_path_smul`, the image of entry `0`
  of `path c` is some entry of `path (σ • c)`.
- `half_pairSMul`: two path components that share a vertex have the same length
  (`IsPathComponent.length_eq` from `RootDatumPathUniqueness`). Hence
  `half (σ • c) = half c`.
- `path_pairSMul`: by `IsPathComponent.eq_or_eq_rev`, the two components sharing
  a vertex agree entrywise, either in order or in reverse order. In the reversed
  case the indices are matched with `Fin.rev` and `Fin.cast` by an `omega`
  computation, using `half_pairSMul`. This is exactly the `path_eq` field, with
  `reverse := false` or `true`.
- `compatibleAction hρ` assembles `pairPerm`, `half_pairSMul` and
  `path_pairSMul`.

## Orbits of the remaining roots

- `restSMul hρ γ a`: the action of `γ` on a remaining root. The image is
  unpaired by `isPaired_apply_iff`, hence again a remaining root.
- `restOrbit hρ a`: the finite set of remaining roots `a'` with
  `ρ γ a = a'` for some `γ`. Every remaining root lies in its own orbit. The orbit
  is closed under `restSMul` (`restSMul_mem_restOrbit`). Any two of its members
  are related by a group element (`exists_apply_of_mem_restOrbit`, using
  `δ * γ⁻¹`). The orbit of any member is the same set (`restOrbit_eq_of_mem`).
- `level_eq_of_mem_restOrbit`: the published `level` (distance from the middle
  pair of the root's path, and `0` for a root on no path) is constant on an orbit.
  This is `level_apply`.
- `isOrthogonal_of_mem_restOrbit`: two distinct members of one orbit are
  orthogonal. They are related by some `ρ γ`, and the first member is unpaired,
  so the published `not_isOrthogonal_of_not_isPaired` applies.

## The ordered orbit blocks

- `restOrbits hρ`: the finite set of all orbits `restOrbit hρ a`. Its elements
  are pairwise disjoint as sets, because two orbits sharing a member are equal.
- `orbitLevel hρ O := O.sup (level ∘ val)`. On an orbit it equals the common
  level of the members (`orbitLevel_restOrbit`, `level_eq_orbitLevel`).
- `sortedOrbits hρ`: `List.mergeSort` of `(restOrbits hρ).toList` by increasing
  `orbitLevel`. It is a permutation of the list of orbits
  (`List.mergeSort_perm`), hence has no duplicates and contains each orbit
  (`nodup_sortedOrbits`, `mem_sortedOrbits`). It is sorted
  (`pairwise_sortedOrbits`, from `List.pairwise_mergeSort` for the total
  preorder `≤` on levels).
- `orbitBlocks hρ`: the list of blocks `O.toList`, one for each `O` in
  `sortedOrbits`. `flatOrbits hρ` is its flattening.
- `nodup_flatOrbits`: each block has no duplicates and distinct blocks are
  disjoint, by `List.nodup_flatten`. `mem_flatOrbits`: every remaining root
  occurs, in the block of its own orbit.
- `pairwise_level_flatOrbits`: levels are weakly increasing along
  `flatOrbits`. Inside a block the level is constant. Across blocks this follows
  from the sorting (`List.pairwise_flatten`). `level_get_le` restates this for
  indices `j' ≤ j`.
- `restOrder hρ : Fin (flatOrbits hρ).length ≃ (pairFamily hρ).Rest` is
  `List.Nodup.getEquivOfForallMemList`. It sends `j` to the `j`-th entry of
  `flatOrbits` (`restOrder_apply`, by `rfl`).
- `isMiddleOut_restOrder`: suppose `order j = path c i` and
  `order j' = path c i'` with `middleDistance (half c) i <
  middleDistance (half c) i'`. If `j' ≤ j`, then `level_get_le` gives
  `level (path c i') ≤ level (path c i)`. The published `level_path` identifies
  these levels with the two middle distances, a contradiction. Hence `j < j'`.
- `invariant_orbitBlocks`: for each block `(restOrbit a).toList` and each `γ`,
  the list of `ρ γ`-images is a permutation of the list of values. Both lists
  have no duplicates, by injectivity of `ρ γ` and of `Subtype.val`. They have the
  same members, by closure of the orbit under `restSMul γ` and `restSMul γ⁻¹`
  (`List.perm_ext_iff_of_nodup`).
- `orbitOrdering hρ : (pairFamily hρ).OrbitOrdering ρ` has `length` the length
  of `flatOrbits`, `order := restOrder hρ` and `blocks := orbitBlocks hρ`.
  - `flatten_eq` is `List.ofFn_get`, read backwards.
  - `invariant` is `invariant_orbitBlocks`.
  - `same_orbit` is `exists_apply_of_mem_restOrbit`.
  - `pairwise`: a block has no duplicates, which gives `a ≠ a'`, and
    `isOrthogonal_of_mem_restOrbit` gives orthogonality.

## The closing theorem

`evenPathOrbitGeometry` introduces the data of the statement and supplies
`J := PairIndex ρ`, `Fintype.ofFinite _`, `C := pairFamily hρ`,
`⟨compatibleAction hρ⟩` and `⟨orbitOrdering hρ⟩`.

Roots on no selected path and unpaired roots on a path both lie in `Rest`, so
every simple root outside the middle pairs is covered by the ordering. Roots on
no path have level `0`. `IsMiddleOut` places no condition on them; they are
only sorted by level together with the other remaining roots.
