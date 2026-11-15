# Full decomposition group over the fixed field of a closed subgroup: proof (M250.005)

This module proves the theorem
`Langlands.NYLL.LocalClassFieldTheory.localAbstractFixedDecompositionGroup_eq_top`.
Its type is the already published closed proposition
`Langlands.NYLL.LocalClassFieldTheory.localAbstractFixedDecompositionGroup_eq_topStatement`
of the module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteSubgroupResidueDegree.U005.Statements`:

```lean
theorem localAbstractFixedDecompositionGroup_eq_top :
    localAbstractFixedDecompositionGroup_eq_topStatement
```

This is the proof phase of M250.005 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m241-m258.md#m250).
No other declaration is added. The theorem has no universe parameter: as in
the source, the field `K` lives in `Type`.

## Target and binders

By its definition in the statement module, the target is

```lean
∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : ClosedSubgroup (Gal(SeparableClosure K/K))),
    decompositionGroup (abstractFixedField K (SeparableClosure K) H)
      (localSeparableValuationSubring K) = ⊤
```

For a nonarchimedean local field `K`, write `B` for the valuation ring
`localSeparableValuationSubring K` of `SeparableClosure K` (M249.006), `H`
for a closed subgroup of `Gal(SeparableClosure K/K)` and
`E = abstractFixedField K (SeparableClosure K) H` (M099.001) for its fixed
field, an intermediate field of `SeparableClosure K / K`. The
`decompositionGroup E B` (M239.001) is Mathlib's
`B.decompositionSubgroup E`, the stabilizer of `B` for the pointwise action
of `SeparableClosure K ≃ₐ[E] SeparableClosure K` on valuation subrings of
`SeparableClosure K`. The statement says this stabilizer is the whole group:
every automorphism `τ` of `SeparableClosure K` over `E` satisfies
`τ • B = B`.

The binders are the source section variables `K` and its four instance
binders (source lines 33–34), followed by the theorem's own binder `H`. No
hypothesis is added. The paired Markdown of the statement module describes
the published declarations in the target.

The proof uses the published M249.010 theorem
`Langlands.NYLL.LocalClassFieldTheory.localSeparableDecompositionGroup_eq_top`,
proved in `LocalResidueDatum.U010.Proofs`, whose type is the closed
proposition `localSeparableDecompositionGroup_eq_topStatement` of
`LocalResidueDatum.U009.Statements`:

```lean
∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    decompositionGroup K (localSeparableValuationSubring K) = ⊤
```

that is, every automorphism of `SeparableClosure K` over `K` preserves `B`.
The two direct imports are the published `U005.Statements` module, which
supplies the target, and the published `LocalResidueDatum.U010.Proofs`
module, which supplies this theorem.

## Implemented proof

```lean
intro K _ _ _ _ H
let A := localSeparableValuationSubring K
apply top_unique
intro tau _htau
let sigma : Gal(SeparableClosure K / K) := tau.restrictScalars K
have hsigma : sigma • A = A := by
  change sigma ∈ decompositionGroup K A
  rw [localSeparableDecompositionGroup_eq_top K]
  exact Subgroup.mem_top sigma
change tau • A = A
exact hsigma
```

1. `intro K _ _ _ _ H` introduces the six binders; `A` names `B`.
2. `apply top_unique` (Mathlib, `a = ⊤` from `⊤ ≤ a`) reduces the goal to
   `⊤ ≤ decompositionGroup E A`. Since `≤` on subgroups is inclusion,
   `intro tau _htau` takes an automorphism
   `tau : SeparableClosure K ≃ₐ[E] SeparableClosure K` with the unused
   hypothesis `tau ∈ ⊤`; the goal is `tau ∈ decompositionGroup E A`.
3. `sigma` is `tau.restrictScalars K`, the same automorphism of
   `SeparableClosure K` regarded as a `K`-algebra automorphism (every
   element of `K` lies in `E`, so `tau` fixes it).
4. `hsigma` proves `sigma • A = A`. `change` restates this goal as
   `sigma ∈ decompositionGroup K A`; membership in the stabilizer is by
   definition the equation `sigma • A = A`. The rewrite with the M249.010
   theorem applied to `K` (`rw` unfolds its closed statement to the equation
   `decompositionGroup K (localSeparableValuationSubring K) = ⊤`) turns the
   goal into `sigma ∈ ⊤`, closed by Mathlib's `Subgroup.mem_top`.
5. `change tau • A = A` restates the main goal by the same unfolding of the
   stabilizer, now for automorphisms over `E`. The pointwise action of an
   automorphism on a valuation subring is induced by its action on
   `SeparableClosure K`, and `sigma` and `tau` act on elements by the same
   function, so `sigma • A` and `tau • A` are definitionally equal; hence
   `exact hsigma` closes the goal.

The development check reports that the theorem has no level parameters and
uses only `propext`, `Classical.choice` and `Quot.sound`, all already used
by the imported definitions and Mathlib; the proof adds no further axiom.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The exact passage is
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteSubgroupResidueDegree.lean`,
lines 80–97](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteSubgroupResidueDegree.lean#L80-L97):
the docstring at 80–82, the signature at 83–86 and the proof at 87–97,

```lean
  let E := abstractFixedField K (SeparableClosure K) H
  let A := localSeparableValuationSubring K
  apply top_unique
  intro tau _htau
  let sigma : Gal(SeparableClosure K / K) := tau.restrictScalars K
  have hsigma : sigma • A = A := by
    change sigma ∈ decompositionGroup K A
    rw [localSeparableDecompositionGroup_eq_top K]
    exact Subgroup.mem_top sigma
  change tau • A = A
  exact hsigma
```

The passage lies in the `LocalClassFieldTheory` namespace (line 20) and its
`noncomputable section` (line 27), with the opens of lines 21–31 and the
section variables `K` and its instance binders at lines 33–34. The complete
original file is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteSubgroupResidueDegree.lean`;
it was read and its SHA-256 hash verified as
`84865498b7b4788c2ebeecb92aeaca7a1bb9a62e2005cb1554386e2a52bf674a`, the hash
recorded in the partition, which records no patch10 change to this module.

| Original declaration | Adapted declaration in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- |
| `LocalClassFieldTheory.localAbstractFixedDecompositionGroup_eq_top` (theorem) | `localAbstractFixedDecompositionGroup_eq_top` (theorem), proving the published target |
| Same theorem's statement | Existing `localAbstractFixedDecompositionGroup_eq_topStatement` |
| `LocalClassFieldTheory.localSeparableDecompositionGroup_eq_top` (M249.010), used by `rw` | Existing published theorem of `LocalResidueDatum.U010.Proofs` |
| `HilbertRamification.ValuationSubring.decompositionGroup`, `abstractFixedField`, `localSeparableValuationSubring` | Existing published definitions (M239.001, M099.001, M249.006) |

Only the first row introduces a declaration here. Modifications by
Worker 127 on 15 November 2026 are:

- add the `Langlands.NYLL` namespace prefix, also in the opened namespace
  `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`,
  and replace the source imports with the `U005.Statements` and
  `LocalResidueDatum.U010.Proofs` imports;
- give the theorem the published closed statement as its type and introduce
  its binders with `intro K _ _ _ _ H`;
- drop the source's first line `let E := abstractFixedField K (SeparableClosure K) H`,
  whose binding `E` is never used in the source proof;
- keep all other source steps unchanged; the name
  `localSeparableDecompositionGroup_eq_top` now denotes the published closed
  M249.010 theorem, applied to `K` as in the source;
- keep only the opens this proof needs, `open scoped Pointwise` (for the
  pointwise action on valuation subrings) and the
  `HilbertRamification.ValuationSubring` namespace (for `decompositionGroup`);
  omit the other source opens, the source `noncomputable section` and all
  other source declarations.

The theorem name and docstring are kept.

The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
Additional attribution material is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Searches of the Library, staging and shared drafts found no earlier proof
port of this theorem.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`,
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. A
development check compiled the module with no diagnostics. This check does
not establish independent semantic acceptance or Integrator publication.

## Attribution and boundary

The original copyright and author header is preserved verbatim:
copyright 2026 Naganori Yamaguchi, author “Naganori Yamaguchi (assisted
by OpenAI Codex)”, released under Apache-2.0. The Lean file carries the
dated modification record. Worker 127 adapted this proof directly from
the pinned original and wrote this companion; Worker 85, who routed the
task, had replayed the same source proof privately, and their task notes
were consulted. No other code or reused draft was supplied. The published
`U005.Statements` and `LocalResidueDatum.U010.Proofs` modules, all other
imported Library modules and their paired Markdown are used unchanged.

The unchanged [LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) remain in the Library
and are byte-identical to the retained originals. Their SHA-256 hashes are
respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No Mathlib code is copied into this file; Mathlib lemmas are only used by
name.

This module proves only M250.005. It does not publish M250.006 or any other
M250 declaration.
