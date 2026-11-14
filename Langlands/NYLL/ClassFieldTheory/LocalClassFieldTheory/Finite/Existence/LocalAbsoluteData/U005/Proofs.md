# NYLL M299.005: base normality makes the abstract fixed field Galois

`Langlands.NYLL.LocalClassFieldTheory.abstractFixedField_isGalois_of_base_normal`
proves the published proposition
`Langlands.NYLL.LocalClassFieldTheory.abstractFixedField_isGalois_of_base_normalStatement K H hnormal`.
The complete source telescope is retained:

```lean
(K : Type) [Field K]
(H : ClosedSubgroup (Gal(SeparableClosure K/K)))
(hnormal :
  (extensionSubgroup
    (baseField (Gal(SeparableClosure K/K))) H
    (le_baseField H)).Normal)
```

The conclusion unfolds to
`IsGalois K (abstractFixedField K (SeparableClosure K) H)`.
Here `K` is any field in universe zero, `H` is a closed subgroup of its
absolute Galois group with the Krull topology, and `hnormal` is normality
inside the distinguished abstract base subgroup. The latter is the whole
absolute Galois group. There are no valuation, finiteness, openness or
local-field assumptions. The explicit hypothesis `hnormal` remains in the
theorem's telescope although it does not occur in the conclusion.

## Implemented proof

Set `B := baseField (Gal(SeparableClosure K / K))`. The published
`CyclicCohomology.extensionSubgroup B H (le_baseField H)` abbreviates exactly
`H.toSubgroup.subgroupOf B.toSubgroup`, so their equality is proved by
reflexivity. Transfer `hnormal` along this equality and apply
`Subgroup.normal_subgroupOf_iff (le_baseField H)` to obtain closure of
`H.toSubgroup` under conjugation by elements of `B.toSubgroup`.
Since `B.toSubgroup = ⊤`, every ambient element lies in it; these conjugation
facts give a local instance of `H.toSubgroup.Normal`.

Apply Mathlib's `InfiniteGalois.normal_iff_isGalois` to the intermediate
field `abstractFixedField K (SeparableClosure K) H`. The published theorem
`closedFixingSubgroup_abstractFixedField_eq K (SeparableClosure K) H`
(M099.002) identifies its closed fixing subgroup with `H`.
Applying `ClosedSubgroup.toSubgroup` to that equality identifies its
ordinary fixing subgroup with `H.toSubgroup`. Rewriting then closes the
normality goal with the local instance. The ambient Galois hypothesis is
Mathlib's instance for the separable closure.

The module imports the fixed published M299.005 target and
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.U002.Proofs`
by their Lean module names. It adds only the requested theorem; the
statement pair and all its imports are unchanged.

## Source and modifications

Adapted by Worker 664 from Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/LocalAbsoluteData.lean`,
M299.005, lines 67–103. The readable source is
[LocalAbsoluteData.lean](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/LocalAbsoluteData.lean>).
The complete file was read and its SHA-256 checked as
`87c3a6b1e9aa5fb2e8ae6602cb8fe6a0a5885f735fecb202c5582ff51567c000`.
Registered sources are `external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`; the public port plan locates
the source row in `notes/reuse/nyll-public-port/m289-m312.md`, section M299.

The source theorem is extracted into this focused `U005/Proofs` module.
Its namespace receives the `Langlands.NYLL` prefix, and its return type is
written using the exact published Prop target. Its binders, names, order,
and binder kinds are unchanged. The proof follows the original route,
with the original `ext sigma; rw [mem_extensionSubgroup_iff]` proof of
`hsub` replaced by `rfl`, verified against the published abbreviation.
Broad source imports are replaced by the two focused published imports.
Unused namespace openings and the unused `noncomputable section` are
omitted. Other source declarations are not copied.

The original copyright, authorship and Apache-2.0 header are retained.
The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` retain
the upstream license and notices.
