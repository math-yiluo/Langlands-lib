# Topological generation: density, generated families and functoriality targets

This module extracts the seven remaining theorem types from Naganori
Yamaguchi's ClassFieldTheory, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, as closed Prop-valued definitions.
It supplies targets only. It contains no proofs of these targets.

The original is
[`Nyll/GaloisCohomology/ProfiniteIntegers/TopologicalGeneration.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/ProfiniteIntegers/TopologicalGeneration.lean),
retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/ProfiniteIntegers/TopologicalGeneration.lean`.
Its SHA-256 is
`c26ef2b96bc95bc63f8030f67e4960a104db989ce2117cc06c0328e67b4fd7fb`.
The full original file was read, including the enclosing section at lines
17–202, its imports, universe declarations and ambient group variables.
The source rows are recorded in
`notes/reuse/nyll-public-port/m001-m024.md`, section M007.

The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original copyright and author header is retained, including Naganori
Yamaguchi's credit for assistance by OpenAI Codex. The retained LICENSE and
NOTICE are `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`; their SHA-256
values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The original NOTICE does not list this source module. No NYLL or
TopologicalGeneration erratum was found in the Library errata notes.
Worker 125 extracted these types directly from the pinned source; no other
worker's draft or compatibility patch was reused.

## Exact source and parameter map

All original names below are in `ClassFormation`; all target names are in
`Langlands.NYLL.ClassFormation`. Append `Statement` to the original final
component to obtain the target's exact name.

Let the ambient telescope mean
`{G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]`.
Let the second-group telescope mean
`{H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]`.
These abbreviations describe the table only; the Lean definitions spell
out every binder. The order in each row follows the complete elaborated
source declaration, with the ambient telescope first wherever it occurs.

| Row and original asserted-type lines | Original name, with `Statement` appended in the target | Complete parameters after the indicated group telescopes | Conclusion |
| --- | --- | --- | --- |
| M007.002, 37–39 | `topologicallyGenerates_iff_dense` | Ambient; `{X : Set G}` | `TopologicallyGenerates X ↔ Dense ((Subgroup.closure X : Subgroup G) : Set G)`. |
| M007.005, 57–61 | `closedSubgroupGeneratedMap_topologicallyGenerates` | Ambient; `{A : Type v}`; `(φ : A → G)` | The range of the canonical `closedSubgroupGeneratedMap φ` topologically generates the actual subgroup underlying `closedSubgroupGenerated (Set.range φ)`. |
| M007.006, 105–109 | `map_mem_closedSubgroupGenerated_image` | Ambient; second group; `(φ : G →ₜ* H)`; `{X : Set G}`; `{y : G}`; `(hy : y ∈ (closedSubgroupGenerated X : Subgroup G))` | `φ y ∈ (closedSubgroupGenerated (φ '' X) : Subgroup H)`. |
| M007.007, 127–133 | `map_mem_closedSubgroupGenerated_singleton` | Ambient; second group; `(φ : G →ₜ* H)`; `(x : G)`; `{y : G}`; `(hy : y ∈ (closedSubgroupGenerated ({x} : Set G) : Subgroup G))` | `φ y ∈ (closedSubgroupGenerated ({φ x} : Set H) : Subgroup H)`. |
| M007.008, 140–144 | `topologicallyGenerates_singleton_of_denseRange_mint` | Second group only; `(f : Multiplicative ℤ →* H)`; `(hf : DenseRange f)` | `TopologicallyGenerates (G := H) ({f (Multiplicative.ofAdd 1)} : Set H)`. |
| M007.009, 174–178 | `topologicallyGenerates_image_of_continuousSurjective` | Ambient; second group; `(f : G →* H)`; `(hf : Continuous f)`; `(hfsurj : Function.Surjective f)`; `{X : Set G}`; `(hX : TopologicallyGenerates (G := G) X)` | `TopologicallyGenerates (G := H) (f '' X)`. |
| M007.010, 191–195 | `topologicallyGenerates_quotient_image` | Ambient; `(N : Subgroup G)`; `[N.Normal]`; `{X : Set G}`; `(hX : TopologicallyGenerates (G := G) X)` | `TopologicallyGenerates (G := G ⧸ N) ((QuotientGroup.mk' N) '' X)`. |

The definitions close the entire source telescope inside `∀`, so their
declaration types are `Prop` rather than functions returning propositions.
Braces, parentheses and instance brackets retain their original binder
kinds. The proof premises `hy`, `hf`, `hfsurj` and `hX` remain named explicit
binders with their original types. Only the unused-variable linter is
disabled locally for the five definitions whose named proof premises do
not occur in their conclusions.

The two universes remain independent: M007.005 uses `G : Type u` and
`A : Type v`; M007.006, M007.007 and M007.009 use `G : Type u` and
`H : Type v`. M007.002 and M007.010 use only `u`. M007.008 uses only `v`,
because the unused ambient `G` and its instances do not occur in the
elaborated original theorem. No topology or group structure is added to
`A`. The dense cyclic-image theorem retains an ordinary monoid homomorphism
and the exact `DenseRange` premise; no continuity assumption is added.
The continuous-surjective theorem retains its ordinary monoid
homomorphism with separate explicit continuity and surjectivity premises.
The two membership targets retain bundled continuous homomorphisms.

## Reuse and extraction changes

The sole import is
`Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.TopologicalGeneration.Definitions`.
It supplies the already published `TopologicallyGenerates`,
`closedSubgroupGenerated` and `closedSubgroupGeneratedMap` definitions,
extracted by Worker 171. The original two Mathlib imports are inherited
through that module. This statement module changes none of those definitions.

The underlying Mathlib constructions were inspected:
`Subgroup.closure`, `Subgroup.topologicalClosure`,
`Subgroup.topologicalClosure_coe`, `Subgroup.topologicalClosure_minimal`,
`ClosedSubgroup` and `DenseRange.topologicalClosure_map_subgroup`.
The last theorem concerns a dense-range homomorphism and a supplied abstract
subgroup with full topological closure. M007.009 instead has the source's
explicit surjectivity premise and its source-specific topological-generation
predicate on a generating set. These targets reuse the actual Mathlib
objects through the published NYLL definitions. No replacement subgroup,
topology, quotient, homomorphism or global instance is introduced.

Changes from the pinned source are the namespace prefix, `Statement`
suffixes, closing the elaborated source telescopes into Prop definitions,
removal of theorem proof bodies, reuse of the published definitions instead
of repeating them, the focused import, local linter settings, and extraction
documentation. Original theorem docstrings, mathematical expressions and
the `Set`, `Topology` and `Pointwise` open directives are retained.
No compatibility patch to the mathematical types is required.

## Signature verification

A private development check compiled an unmodified copy of the complete
pinned source with the approved Lean 4.34.0 environment. For every one of
the seven source theorems, it compared the original declaration type with
the value of the corresponding closed target. All seven comparisons passed:
the universe-parameter lists and every successive `forall` binder kind
agree exactly, and the complete types are definitionally equal after
unfolding the original and adapted definitions. Separate checks assigned
each unapplied original theorem constant directly to the corresponding
target with explicit universe arguments. These checks include the
single-universe `v` signature of M007.008.

The private original-source and audit modules are excluded from this
contribution. They establish the source correspondence of the target
definitions during development and do not publish proofs of those targets.

These seven targets do not assert a proved class-formation, cup, Tate,
transfer or cohomological reciprocity result. Proofs of the source theorems
remain separate work after target publication.
