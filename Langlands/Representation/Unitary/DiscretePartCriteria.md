# Criteria for membership in the discrete part

Module `Langlands.Representation.Unitary.DiscretePartCriteria` proves two criteria for
`Langlands.Analysis.discretePart` (module `Langlands.Representation.Unitary.DiscretePart`), the
closure of the sum of the irreducible subrepresentations of a representation
`ρ : Representation ℂ H E` on a complex inner product space. It states no proposition
definition; every declaration is a proved theorem. All names are in the namespace
`Langlands.Analysis`.

| Declaration | Kind | Source |
| --- | --- | --- |
| `discretePart_le_of_forall_le` | theorem (proved) | internal |
| `le_discretePart` | theorem (proved) | internal |
| `inner_map_map_of_norm` | theorem (proved) | internal |
| `map_map_inv` | theorem (proved) | internal |
| `orthogonal_invariant` | theorem (proved) | internal |
| `mem_discretePart_of_starProjection_mem` | theorem (proved) | internal |

## Provenance

The results are elementary facts about unitary representations on Hilbert spaces. The second
criterion is the abstract form of the classical argument that a square-integrable automorphic
form generates a finite sum of irreducible subrepresentations of `L²([G])`: the projections of
the form onto the summands of any orthogonal decomposition of the closed invariant subspace it
generates are nonzero, mutually orthogonal and lie in a finite-dimensional space of automorphic
forms of one type, so a decomposition with the most summands has irreducible summands
(compare Getz–Hahn, *An introduction to automorphic representations* (2024), registered as
`getz-hahn-2024-automorphic-representations`, Theorem 6.3.4, printed p.164, for the
finite-dimensional space). The Lean proof below does not choose a maximal decomposition; it
argues by induction on a dimension.

## Statements

Throughout, `E` is a complex inner product space. `H` is a monoid for the first two theorems and
a group for the others; for the last theorem `E` is complete.

- `discretePart_le_of_forall_le ρ hS h`: if `S` is a closed subspace of `E` that contains every
  irreducible subrepresentation of `ρ`, then `discretePart ρ ≤ S`.
- `le_discretePart ρ hV`: an irreducible subrepresentation `V` of `ρ` satisfies
  `V ≤ discretePart ρ`.
- `inner_map_map_of_norm hρ h x y`: if every `ρ h` preserves norms, then
  `⟪ρ h x, ρ h y⟫ = ⟪x, y⟫`.
- `map_map_inv ρ h x`: `ρ h (ρ h⁻¹ x) = x`.
- `orthogonal_invariant hρ hV`: if every `ρ h` preserves norms and `V` is `ρ`-invariant, then the
  orthogonal complement `Vᗮ` is `ρ`-invariant.
- `mem_discretePart_of_starProjection_mem ρ hρ v W hW`: let every `ρ h` preserve norms, let
  `v ∈ E`, and let `W` be a finite-dimensional subspace of `E` such that, for every subspace `V`
  of `E` that has an orthogonal projection (`V.HasOrthogonalProjection`) and is `ρ`-invariant,
  the orthogonal projection `V.starProjection v` lies in `W`. Then `v ∈ discretePart ρ`.

In a Hilbert space the subspaces with an orthogonal projection are exactly the closed ones, so
the hypothesis of the last theorem concerns the projections of `v` onto all closed invariant
subspaces. No continuity of `h ↦ ρ h x` is assumed.

## Proofs

- `discretePart_le_of_forall_le`: the supremum of the irreducible subrepresentations lies in `S`
  (`sSup_le`), and `S` is closed, so the topological closure of that supremum lies in `S`
  (`Submodule.topologicalClosure_minimal`).
- `le_discretePart`: `le_sSup` followed by `Submodule.le_topologicalClosure`.
- `inner_map_map_of_norm`: polarization, `LinearMap.norm_map_iff_inner_map_map`.
- `map_map_inv`: `ρ h * ρ h⁻¹ = ρ (h h⁻¹) = 1`.
- `orthogonal_invariant`: for `x ∈ Vᗮ` and `u ∈ V`, write `u = ρ h (ρ h⁻¹ u)`; then
  `⟪u, ρ h x⟫ = ⟪ρ h⁻¹ u, x⟫ = 0` because `ρ h⁻¹ u ∈ V`.
- `mem_discretePart_of_starProjection_mem`. Call a subspace closed invariant if it is closed and
  `ρ`-invariant. Every closed subspace `V` of the complete space `E` has an orthogonal
  projection, so `w ∈ V` and `v - w ∈ Vᗮ` imply `w = V.starProjection v ∈ W`
  (`eq_starProjection_of_mem_orthogonal`); every `x` decomposes as `y + (x - y)` with `y ∈ V`,
  `x - y ∈ Vᗮ`. Intersections and orthogonal complements of closed invariant subspaces are
  closed invariant (`orthogonal_invariant`).
  1. Let `C` be the infimum of all closed invariant subspaces containing `v`. It is closed (an
     intersection of closed sets, `Submodule.coe_sInf`), invariant, contains `v`, and lies in
     every closed invariant subspace containing `v`.
  2. If `X ≤ C` is closed invariant and nonzero, the projection of `v` onto `X` is nonzero:
     otherwise `v ∈ Xᗮ`, which is closed invariant, so `X ≤ C ≤ Xᗮ` and `X = 0`.
  3. For a subspace `X` let `T X` be the span of the projections of `v` onto the closed
     invariant subspaces `Y ≤ X`. It lies in `W`, so it is finite-dimensional; let `d X` be its
     dimension.
  4. If `Y ≤ X ≤ C` are closed invariant and `Y ≠ X`, then `d Y < d X`. Indeed `T Y ≤ T X`.
     The subspace `Z = X ⊓ Yᗮ` is closed invariant and nonzero: if it were zero, every `x ∈ X`
     would satisfy `x - y ∈ Z = 0` for its component `y ∈ Y`, so `X = Y`. By step 2 the
     projection `w` of `v` onto `Z` is nonzero. It lies in `T X`. It is orthogonal to every
     projection onto a closed invariant `Y' ≤ Y`, since `w ∈ Yᗮ`, hence to `T Y`; as `w ≠ 0`,
     `w ∉ T Y`. So `T Y < T X` and `Submodule.finrank_lt_finrank_of_lt` applies.
  5. Every nonzero closed invariant `X ≤ C` contains an irreducible subrepresentation: take a
     nonzero closed invariant `Y ≤ X` with the least value of `d` (`Nat.find`). A closed
     invariant `Y' ≤ Y` other than `0` and `Y` would have `d Y' < d Y` by step 4.
  6. By strong induction on `d X`, every closed invariant `X ≤ C` lies in the sum of the
     irreducible subrepresentations. If `X ≠ 0`, take an irreducible `Y ≤ X` (step 5). The
     subspace `X ⊓ Yᗮ` is closed invariant and differs from `X` (otherwise `Y ≤ Yᗮ` and
     `Y = 0`), so by step 4 and the induction hypothesis it lies in the sum. Every `x ∈ X` is
     `y + (x - y)` with `y ∈ Y` and `x - y ∈ X ⊓ Yᗮ`.
  7. Applied to `X = C`, this gives `v ∈ C ≤ sSup {irreducible} ≤ discretePart ρ`.

The module uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Use

`Langlands.Global.groupSquareIntegrableFormSpectrum_of_reduction` (module
`Langlands.Global.AdelicGroupDiscreteSpectrumReduction`) applies the two criteria to the right
regular representation of `G(𝔸)` on `L²([G])`.
