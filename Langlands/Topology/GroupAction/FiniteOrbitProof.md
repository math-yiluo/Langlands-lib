# Proof of finite orbit ordering for continuous group actions

This module proves the published statement
`Langlands.Topology.FiniteOrbitOrdering` from
`Langlands.Topology.GroupAction.FiniteOrbitStatement`. The closing theorem is

```lean
theorem Langlands.Topology.finiteOrbitOrdering : FiniteOrbitOrdering.{uH, uX}
```

It is unapplied, and the group universe `uH` and space universe `uX` are
independent. The statement module is imported unchanged.

## Result

Let `H` be a sigma-compact topological group acting continuously on a locally
compact Hausdorff space `X`, and suppose the Mathlib orbit quotient
`MulAction.orbitRel.Quotient H X` is finite. Then there are `n` and
`r : Fin n → X` such that:

- the orbits `MulAction.orbit H (r i)` cover `X`;
- these orbits are pairwise disjoint;
- for each `k : Fin (n + 1)`, the union of the first `k` orbits is open.

The empty space is covered by the case `n = 0`. The proof needs no extra
hypotheses. It assumes no local closedness of orbits, no existing ordering,
no local compactness, zero-dimensionality or second countability of the group,
and no second countability of `X`. The instance `IsTopologicalGroup H` is part of
the statement's telescope but is not used. The proof only needs each
`h • -` to be a homeomorphism, which follows from `ContinuousSMul H X` because
`H` is a group.

## Implemented proof

The auxiliary declarations live in the namespace
`Langlands.Topology.FiniteOrbitProof`.

### An orbit that is relatively open in a closed invariant set

`exists_relOpen_orbit` states the following. Let `C ⊆ X` be closed, nonempty and
`H`-invariant, meaning `x ∈ C → h • x ∈ C`. Then there are `y ∈ C` and an open
set `V ⊆ X` with `V ∩ C = orbit H y`.

1. *Countable closed cover.* For each orbit class `q` and each `m : ℕ`, let
   `A (q, m)` be the image of Mathlib's compact set `compactCovering H m` under
   `h ↦ h • q.out`. Each `A (q, m)` is compact, hence closed in the Hausdorff
   space `X`, and it lies in `orbit H q.out`. Every `z : X` lies in the orbit of
   `(⟦z⟧).out`, so `z = g • (⟦z⟧).out` for some `g`. Since
   `⋃ m, compactCovering H m = univ`, `g` lies in some `compactCovering H m`.
   Hence the sets `A (q, m)` cover `X`. The index type
   `orbitRel.Quotient H X × ℕ` is countable because the quotient is finite.
2. *Baire category in `C`.* As a closed subspace, `C` is locally compact
   (`IsClosed.locallyCompactSpace`) and Hausdorff, so it is a Baire space
   (`BaireSpace.of_t2Space_locallyCompactSpace`), and it is nonempty. The
   preimages of the sets `A (q, m)` in `C` are closed and cover `C`. By
   `nonempty_interior_of_iUnion_of_closed`, one preimage `f p` has nonempty
   interior. That interior is open in the subspace topology, so it is the
   preimage of an open set `W ⊆ X` (`isOpen_induced_iff`). Pick a point `y` of
   the interior. Then `y ∈ W ∩ C`, and `W ∩ C ⊆ A p ⊆ orbit H p.1.out`. Since
   `y` lies in that orbit, `orbit H p.1.out = orbit H y`, so
   `W ∩ C ⊆ orbit H y`.
3. *Translation.* Put `V = ⋃ h : H, h • W`. This set is open because each
   `h • W` is open (`IsOpen.smul`). If `z ∈ h • W ∩ C`, then `h⁻¹ • z ∈ W`, and
   `h⁻¹ • z ∈ C` by invariance. Hence `h⁻¹ • z ∈ orbit H y`, so
   `z ∈ orbit H y`. Conversely, `g • y ∈ g • W` because `y ∈ W`, and
   `g • y ∈ C` by invariance. Therefore `V ∩ C = orbit H y`.

### Induction on the number of orbits

`exists_ordering_of_closed` proves a relative version by strong induction on
`N`, the `Set.ncard` of the image of `C` in the orbit quotient. For every closed
invariant `C` with this count `N`, there are `n` and `r : Fin n → X` such that:

- each `r i` lies in `C`;
- the orbits of the `r i` cover `C` and are pairwise disjoint;
- for each `k : Fin (n + 1)`, the set `Cᶜ ∪ {x | ∃ i, i < k ∧ x ∈ orbit H (r i)}`
  is open.

- If `C = ∅`, take `n = 0`. Every set in the last condition is
  `univ ∪ ∅ = univ`.
- Otherwise `exists_relOpen_orbit` gives `y ∈ C` and an open `V` with
  `V ∩ C = orbit H y`. Let `C' = C ∩ Vᶜ`. It is closed. It is also invariant: if
  `h • x ∈ V` for some `x ∈ C'`, then `h • x ∈ orbit H y`, so
  `x ∈ orbit H y ⊆ V`, a contradiction. Its orbit image is a strict subset of
  that of `C`, because the class of `y` is missing. A point of `C'` in the class
  of `y` would lie in `orbit H y ⊆ V`. Hence `Set.ncard_lt_ncard` lowers the
  count, and the induction hypothesis applies to `C'`, giving `n` and `r`.
- The new enumeration is `Fin.cons y r` of length `n + 1`. A point of `C` lies
  either in `V` and hence in `orbit H y`, or in `C'` and hence in some
  `orbit H (r j)`. The orbit of `y` is disjoint from each `orbit H (r j)`.
  Otherwise the two orbits would coincide (`orbit_eq_iff`), which would put
  `r j ∈ orbit H y ⊆ V`, contrary to `r j ∈ C'`. The remaining pairs are
  disjoint by the induction hypothesis.
- For openness, `k = 0` gives `Cᶜ`, which is open. For `k = j + 1`, the
  initial union of `Fin.cons y r` is `orbit H y ∪ S_j`, where `S_j` is the
  initial union of `r` with `j` members. Using `orbit H y ⊆ V` and
  `V ∩ C ⊆ orbit H y`, we get
  `Cᶜ ∪ (orbit H y ∪ S_j) = (C ∩ Vᶜ)ᶜ ∪ S_j`. The right side is open by the
  induction hypothesis.

### The closing theorem

`finiteOrbitOrdering` applies `exists_ordering_of_closed` with `C = univ`. This
set is closed and invariant, and `N` is the `ncard` of its orbit image. Since
`univᶜ = ∅`, the relative openness conditions become openness of the initial
unions, and the cover condition gives the cover of `X`. Only the axioms
`propext`, `Classical.choice` and `Quot.sound` are used.

## Relation to the literature

The statement is an internal generalization motivated by Bernstein–Zelevinsky
(1976), section 1.5, printed/PDF page 7 (`bernstein-zelevinsky-1976-representations-gln`),
and Bernstein–Zelevinsky (1977), section 5.1, printed pages 459–460
(`bernstein-zelevinsky-1977-induced-i`). The statement's Markdown records the
provenance. The proof here follows the plan in that Markdown: a Baire category
argument on a countable compact cover, an open orbit obtained by translation, and
induction on closed invariant complements. It does not reproduce the sources'
claim that a suitable orbit map is open, and it does not use their compact open
subgroup basis. The ordering conclusion does not need either.
