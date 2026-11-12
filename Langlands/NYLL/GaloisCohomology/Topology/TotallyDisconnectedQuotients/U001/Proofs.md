# Closed-normal quotients of profinite groups: M013.001 proof

This module proves
`Langlands.NYLL.QuotientGroup.totallyDisconnectedSpace_of_isClosed.{u}`
with type exactly
`Langlands.NYLL.QuotientGroup.totallyDisconnectedSpace_of_isClosedStatement.{u}`,
the closed proposition in [Statements](Statements.md). It applies to every
universe `u` and the actual Mathlib quotient group `G ⧸ N` with its quotient
topology.

Unfolding the imported proposition gives the complete telescope:

```lean
∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)),
  TotallyDisconnectedSpace (G ⧸ N)
```

The theorem has no additional parameters: its proof introduces these ten
binders with `intro G _ _ _ _ _ _ N _ hN`. Their order, implicit or
instance-implicit status, hypotheses and universe are fixed by the imported
target. `N` is any closed normal subgroup; there is no finiteness condition
on `N`. The quotient type and topology are exactly those in the target.

## Implemented proof

The proof follows Yamaguchi's source argument without changing its tactic
body. Let `q : G →* G ⧸ N` be `QuotientGroup.mk' N`. To separate unequal
quotient points, choose representatives `x` and `y` using surjectivity of
`q`. Their difference `g = x⁻¹ * y` does not belong to `N`, since otherwise
`q x = q y`.

The set `W = {u | g * u⁻¹ ∉ N}` is open: it is the inverse image of the
open complement of `N` under the continuous map `u ↦ g * u⁻¹`. It contains
`1`. The profinite open-normal-subgroup theorem supplies an open normal
subgroup `V` contained in `W`. Set `K = N ⊔ V`. It is open because it
contains the open subgroup `V`, and it contains `N`. If `g ∈ K`, normality
of `V` writes `g = n * v` with `n ∈ N` and `v ∈ V`. But `v ∈ W` says
`g * v⁻¹ ∉ N`, contradicting `g * v⁻¹ = n`. Thus `g ∉ K`.

Its image `Kbar = K.map q` is an open subgroup of the quotient because
the quotient map is open. The kernel of `q` is `N`, which is contained in
`K`; hence `Kbar.comap q = K`. It follows that `q g ∉ Kbar`. An open
subgroup is also closed. Pulling this clopen subgroup back under the
continuous translation `z ↦ (q x)⁻¹ * z` gives a clopen set containing
`q x` and excluding `q y`.

This constructs the pairwise clopen separators required by
`totallySeparatedSpace_iff_exists_isClopen`. The proof installs the resulting
`TotallySeparatedSpace (G ⧸ N)` only locally and obtains
`TotallyDisconnectedSpace (G ⧸ N)` by Mathlib's standard instance. The
module adds no global instance or simp attribute.

## Actual dependencies

The sole direct import is the published Statements module. It imports
`Mathlib.Topology.Algebra.ClopenNhdofOne` and
`Mathlib.Topology.Algebra.Group.Quotient`, the two original source imports.
The proof uses these Mathlib results through that import:

- `QuotientGroup.mk'_surjective`, `eq_one_iff` and `ker_mk'` identify
  quotient representatives and the quotient homomorphism's kernel.
- `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one` supplies
  `V`. Its compact and totally disconnected group hypotheses are exactly
  available from the target.
- `Subgroup.mem_sup_of_normal_right` gives the product description of
  `N ⊔ V`, and `Subgroup.isOpen_of_openSubgroup` proves it open.
- `QuotientGroup.isOpenMap_coe`, `Subgroup.comap_map_eq_self` and
  `Subgroup.isClosed_of_isOpen` supply the image-subgroup facts.
- Continuity of inversion and multiplication, together with the standard
  topological-group instance on a normal quotient, makes the two inverse
  images continuous.
- `totallySeparatedSpace_iff_exists_isClopen` and
  `TotallySeparatedSpace.totallyDisconnectedSpace` finish the argument.

No other NYLL result or unpublished worker draft is used. The published
Statements Lean/Markdown pair, its imports, and the retained licenses are
unchanged. The other source units M013.002–M013.004 remain separate work.
This topological support proof asserts no host class-formation, cup-product,
Tate-cohomology, transfer or reciprocity result.

## Source correspondence and attribution

The source is Naganori Yamaguchi's
[ClassFieldTheory](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[Nyll/GaloisCohomology/Topology/TotallyDisconnectedQuotients.lean, lines 21–97](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Topology/TotallyDisconnectedQuotients.lean#L21-L97).
The complete 187-line original was read. Its SHA-256 is
`cab3604efecf0e48f740c668abf5d2e22aa1436172cf5f6bb8c1e6c72ed72c63`.
The inventory's endpoint 95 falls inside the proof; the extraction includes
its final `infer_instance` at line 97.

The original theorem is `QuotientGroup.totallyDisconnectedSpace_of_isClosed`.
The adaptation adds the `Langlands.NYLL` namespace prefix and declares the
required theorem directly of the already published closed proposition.
After introducing that proposition's binders, the tactic body at source
lines 28–97 is copied unchanged. Thus the proof route is unchanged. The
original two imports are supplied through Statements, the module docstring
is focused on this proof, and the other three source declarations are
omitted. Worker 171 made these adaptations on 11 November 2026.

The original author, copyright and Apache-2.0 header is preserved verbatim,
including the attribution “Naganori Yamaguchi (assisted by OpenAI Codex)”.
The retained [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) match the pinned originals,
with SHA-256 hashes
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

The original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
and attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The pinned snapshot is under
`n-yamaguchi-0729--ClassFieldTheory/source/` in the project's
“External Lean project reuse survey- pinned source snapshots, 21 October
2026” literature folder. No `notes/errata/<source id>.md` for either ID was
found in this workspace, the project or Library base
`0ef479821d752edef9ef540203ddfb7f637bbce6`.

## Development validation

`lean_check` diagnostic `da6e13d8-e740-4dc5-a879-e0cc7d0a6153` in
environment `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` compiled this proof
module with zero errors and warnings. Inspection reports a theorem with
the single universe parameter `u` and exactly the standard axioms
`propext`, `Classical.choice` and `Quot.sound`. The environment is
Lean 4.34.0 with Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
This development check establishes compilation and declaration inspection;
formal exact-target validation, independent acceptance and publication
are separate submission procedures.
