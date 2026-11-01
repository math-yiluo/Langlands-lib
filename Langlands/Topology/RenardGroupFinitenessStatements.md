# Renard II.3.2: finite, discrete and countable coset quotients

This module contains **statements**, expressed as three closed `Prop`-valued
definitions and their closed conjunction. It provides no proof of these
assertions.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated **9 July 2026**, II.3.2, “Un résultat de finitude,” the complete lemma and
proof on printed page **43** / PDF page **49**:

- Literature ID: `renard-2026-representations-groupes-reductifs-padiques`.
- Original: `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
- SHA256: `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

Worker 450 read that entire PDF page and the t.d.-space and group definitions
in II.1.1, printed page 30 / PDF page 36, and checked the original file's hash.
The latter definition requires Hausdorffness and a compact-open neighborhood
basis. It is exactly the published predicate
`Langlands.Topology.IsLocallyProfinite G`, which is equivalent, by
`Langlands.Topology.isLocallyProfinite_iff_mathlib`, to
`T2Space G ∧ LocallyCompactSpace G ∧ TotallyDisconnectedSpace G`.

The registered supplementary source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read on PDF pages 2–3. It is the author's corrections to the 2010 edition,
retained at
`literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`.
PDF page 3 distinguishes second countability, countable neighborhood bases,
separability and sigma-compactness. The 2026 original governs these statements.
The source's countable increasing compact exhaustion is equivalent to
`SigmaCompactSpace G`: finite unions make any countable compact cover
increasing.

## Actual quotients and source hypotheses

Every declaration quantifies over `G : Type u` in an arbitrary universe, with
its supplied `[Group G]`, `[TopologicalSpace G]` and `[IsTopologicalGroup G]`.
The assumption `IsLocallyProfinite G` concerns that same topology. The
subgroups are actual `Subgroup G` objects; compactness and openness concern
their underlying sets in this topology.

Mathlib's `G ⧸ K` is `Quotient (QuotientGroup.leftRel K)`. Its relation is
`x⁻¹ * y ∈ K`, so the class of `g` is the set `gK`. This agrees with the sets
explicitly used in Renard's proof, although the source's prose calls its
classes right cosets. Mathlib calls these left cosets. No normality of `K` is
required to construct this quotient type.

The topology in `QuotientDiscrete` is the existing
`QuotientGroup.instTopologicalSpace K`, definitionally
`instTopologicalSpaceQuotient`: the ordinary quotient topology coinduced by
the projection from the supplied topology of `G`. No discrete topology is
installed as input. Countability concerns this very same carrier `G ⧸ K`.
There is no assumed quotient group or replacement discrete carrier.

For `K ≤ K1`, `K.subgroupOf K1` is the subgroup of the actual subgroup type
`K1` defined by membership in `K`; nesting identifies it with `K` inside
`K1`. The relative quotient `K1 ⧸ K.subgroupOf K1` is therefore the genuine
coset space for the index `[K1 : K]`. The topology of `K1` is its induced
subtype topology, and the relative quotient inherits its ordinary quotient
topology. Its finiteness assertion is `Finite` of the carrier itself.

With prefix `Langlands.Topology.RenardGroupFinitenessStatements.`:

| Declaration | Complete source-scoped conclusion |
| --- | --- |
| `RelativeQuotientFinite` | For every t.d. topological group and subgroups `K`, `K1`, if both subgroups are compact and open and `K ≤ K1`, then `Finite (K1 ⧸ K.subgroupOf K1)`. |
| `QuotientDiscrete` | For every t.d. topological group and compact open subgroup `K`, `DiscreteTopology (G ⧸ K)` holds for the ordinary quotient topology. |
| `QuotientCountable` | For every t.d. topological group with `[SigmaCompactSpace G]` and compact open subgroup `K`, `Countable (G ⧸ K)` holds. |
| `Assertions` | The closed conjunction `RelativeQuotientFinite.{u} ∧ QuotientDiscrete.{u} ∧ QuotientCountable.{u}`. |

Only the third assertion assumes sigma-compactness. None assumes normality,
second countability, separability, a matrix realization, or
`NonarchimedeanGroup G`. There is no extra nonemptiness assumption: the
identity element gives an identity coset in both quotients. All source
compactness and openness hypotheses are retained, even where a stronger
general theorem could omit some of them.

## Proof boundary and environment

Renard's relative-finiteness proof covers the compact subgroup `K1` by
disjoint open cosets and extracts a finite subcover. For countability, a
finite family of open cosets covers each compact member of a countable
compact exhaustion, giving a countable cover of `G` by cosets.

These arguments describe the original source, not proofs implemented here.
The three conclusions remain proof obligations. A separate focused proof
successor must prove the unchanged published declaration
`Langlands.Topology.RenardGroupFinitenessStatements.Assertions`; its Markdown
must describe its implemented Lean route, which may use existing Mathlib
results instead of the source's finite-subcover argument.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0 at
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib at
`5ed2965256430c3649e86755f9576b54eca72435`. The project dependency is
`Langlands.Topology.LocallyProfinite`. Mathlib imports supply the existing
coset quotient topology and sigma-compactness class. No new axiom or
mathematical construction is introduced.
