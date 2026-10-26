# Renard's t.d. spaces and Mathlib local profiniteness

`Langlands.Topology.IsLocallyProfinite X` expresses exactly Renard's t.d.-space
definition: the supplied topological space is Hausdorff and every neighborhood
of every point contains a compact open set containing that point. The name
"locally profinite" distinguishes this predicate from Mathlib's weaker
`TotallyDisconnectedSpace X`. It introduces no topology or typeclass.

## Source and correspondence

The original is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated **9 July 2026**, II.1.1, printed page 30 / PDF page 36,
opening space and group definitions.

- Literature ID: `renard-2026-representations-groupes-reductifs-padiques`.
- Original: `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
- SHA256: `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
- Worker 595 checked the title/date, 296-page count and full hash and read PDF
  page 36 in full.

The source explicitly requires a separated space and a neighborhood basis of
compact opens at each point. Here separated means Hausdorff, implemented by
`T2Space X`. The compactness predicate is Mathlib's `IsCompact`; Hausdorffness
of the ambient space supplies the separation convention. There is no
countability, second-countability, sigma-compactness, nonemptiness, group or
ring assumption on the space definition.

The registered supplementary source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
is retained at
`literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`.
Its opening corrections, in particular PDF page 2's Baire correction at printed
2010 page 35, were checked. The governing 2026 page already states that
countable intersections of dense opens are dense. This is a source check;
the Baire proposition is a separate successor.

## Transparent predicates and basis laws

Both definitions are `Prop`-valued and universe-polymorphic in `X : Type u`,
with `[TopologicalSpace X]` as an actual supplied instance.

```lean
HasCompactOpenNeighborhoodBasis X :=
  ∀ (x : X) (U : Set X), U ∈ 𝓝 x →
    ∃ V : Set X, x ∈ V ∧ IsOpen V ∧ IsCompact V ∧ V ⊆ U

IsLocallyProfinite X :=
  T2Space X ∧ HasCompactOpenNeighborhoodBasis X
```

These names are in `Langlands.Topology`. The auxiliary basis predicate does
not impose separation. The pointwise quantifier permits arbitrary
neighborhoods `U`; `U` need not be open. Every witness `V` is a neighborhood
because it is open and contains `x`. This gives the source's neighborhood
basis condition directly.

The following are short intrinsic laws, proved in the same definition unit:

| Declaration, with prefix `Langlands.Topology.` | Content |
| --- | --- |
| `HasCompactOpenNeighborhoodBasis.mem_nhds_iff` | Membership in `𝓝 x` is equivalent to containing a compact open set containing `x`. |
| `HasCompactOpenNeighborhoodBasis.nhds_hasBasis` | The corresponding `Filter.HasBasis` with set index `V`, predicate `x ∈ V ∧ IsOpen V ∧ IsCompact V`, and value `id V`. |
| `HasCompactOpenNeighborhoodBasis.isTopologicalBasis` | All compact open subsets form a topological basis. |
| `hasCompactOpenNeighborhoodBasis_iff_isTopologicalBasis` | Equivalence of the pointwise condition and that topological-basis assertion. |
| `isLocallyProfinite_iff_isTopologicalBasis` | The same equivalence with the explicit `T2Space X` conjunct. |
| `HasCompactOpenNeighborhoodBasis.locallyCompactSpace` | A compact-open neighborhood basis supplies `LocallyCompactSpace X`, without separation. |
| `IsLocallyProfinite.t2Space`, `.hasCompactOpenNeighborhoodBasis`, `.locallyCompactSpace`, `.totallyDisconnectedSpace` | Explicit extraction/conversion lemmas from the source predicate. |
| `hasCompactOpenNeighborhoodBasis_of_mathlib`, `isLocallyProfinite_of_mathlib` | Reverse conversions under `[T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]`. |
| `isLocallyProfinite_iff_mathlib` | `IsLocallyProfinite X ↔ T2Space X ∧ LocallyCompactSpace X ∧ TotallyDisconnectedSpace X`. |
| `isLocallyProfinite_of_weaklyLocallyCompactSpace` | Reverse conversion using weak local compactness and explicit Hausdorffness and total disconnectedness. |
| `isLocallyProfinite_iff_weaklyLocallyCompactSpace` | The corresponding equivalence with the three conjuncts `T2Space X`, `WeaklyLocallyCompactSpace X`, `TotallyDisconnectedSpace X`. |

The neighborhood and topological-basis laws unpack the definitions and use
Mathlib's `isTopologicalBasis_of_isOpen_of_nhds` and
`IsTopologicalBasis.mem_nhds_iff`. Local compactness follows by taking the same
compact open witness in each neighborhood.

For the forward total-disconnectedness conversion, install the extracted
`T2Space X` locally. Every compact open is closed in this Hausdorff space,
so the compact-open basis enlarges to the basis of all clopens. Mathlib's
`totallySeparatedSpace_of_t0_of_basis_clopen` supplies total separatedness,
and its existing instance supplies total disconnectedness.

For the reverse conversion, `local_compact_nhds` first supplies a compact
neighborhood `C ⊆ U`. Mathlib's
`loc_compact_Haus_tot_disc_of_zero_dim` supplies a clopen neighborhood
`V ⊆ C`. Since `V` is closed and contained in the compact set `C`,
`IsCompact.of_isClosed_subset` makes it compact. Its openness, point membership
and inclusion in `U` give exactly the required witness. This internal
Mathlib proof route establishes the definition correspondence; it does not use
the source's later subspace or refinement lemmas.

Mathlib's `WeaklyLocallyCompactSpace X` only requires one compact neighborhood
at every point. `LocallyCompactSpace X` requires a compact neighborhood inside
every neighborhood. They differ without separation. Local compactness always
implies weak local compactness. The reverse direction used here is Mathlib's
`WeaklyLocallyCompactSpace.locallyCompactSpace` under `R1Space X`; `T2Space X`
provides that hypothesis. The weak-local equivalence explicitly installs this
existing conversion before applying the reverse Mathlib correspondence.

These conversions return proofs of the existing Mathlib classes. They do not
register new global instances. A consumer may, for example, use
`let : LocallyCompactSpace X := h.locallyCompactSpace`.

## Groups over the same topology

For an actual type `G : Type u` with `[Group G] [TopologicalSpace G]` and
`[IsTopologicalGroup G]`, the assumption
`h : Langlands.Topology.IsLocallyProfinite G` is precisely the source's
definition of a t.d. topological group: its underlying space is t.d. Both the
group's continuity assumptions and the space predicate use that same supplied
topology.

The two group conversion laws have the additional explicit assumption
`[NonarchimedeanGroup G]`, which already extends `IsTopologicalGroup G`:

- `isLocallyProfinite_of_nonarchimedean` assumes `[T2Space G]` and
  `[WeaklyLocallyCompactSpace G]`. Mathlib's Hausdorff nonarchimedean
  total-separatedness instance supplies total disconnectedness, and the weak
  local conversion above supplies the source predicate.
- `IsLocallyProfinite.compactOpenSubgroupBasis h` retains
  `[NonarchimedeanGroup G]` and returns, for every `U ∈ 𝓝 (1 : G)`, an
  `OpenSubgroup G` whose underlying set is compact and contained in `U`.
  Its proof extracts local compactness from `h`, obtains weak local compactness
  through Mathlib, and applies the existing
  `Langlands.compactOpenSubgroupBasis G`.

The imported Library theorem is in
`Langlands.Topology.CompactOpen.NeighborhoodBasis`, with target
`Langlands.CompactOpenSubgroupBasis` in the corresponding `Statement` module.
Its exact hypotheses are `[Group G] [TopologicalSpace G]`,
`[NonarchimedeanGroup G]` and `[WeaklyLocallyCompactSpace G]`; it requires
no Hausdorffness. Its open subgroup comes from a compact neighborhood
intersected with the requested neighborhood, then compactness follows from
closedness of open subgroups. Thus it already applies under the source
predicate **when the nonarchimedean assumption is also provided**.

Hausdorffness remains explicit when relating these hypotheses to Renard.
Nonarchimedean groups with weak or strong local compactness need not be
Hausdorff; a nontrivial finite group with the indiscrete topology gives an
elementary example. The source's compact-open subgroup characterization is
therefore understood within Hausdorff topological groups.

Deriving `NonarchimedeanGroup G` from `IsLocallyProfinite G` and
`IsTopologicalGroup G` is the separate Van Dantzig obligation. Neither group
law here performs that derivation.

## Dependencies and successors

The only project import is the already published compact-open subgroup basis
module. Mathlib imports are
`Mathlib.Topology.Separation.Profinite` and
`Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected`.
The approved environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`:
Lean 4.34.0 at commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`,
Mathlib at commit `5ed2965256430c3649e86755f9576b54eca72435`.
This unit is independent of the Renard idempotented-ring core.

The definition is source-derived; the auxiliary predicate, equivalences and
conversion proofs are intrinsic consequences using the named Mathlib and
Library interfaces. No new axiom is introduced.

Separate successors at the same source locator are Van Dantzig's theorem,
the locally closed subspace lemma, the finite subordinate pairwise-disjoint
compact-open refinement lemma, and the Baire proposition. The refinement
sets need not lie inside the compact set being covered. None of these source
results is assumed or proved in this definition unit.
