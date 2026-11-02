# Antitone filtrations by normal subgroups

This module adapts exactly M224.001–.002 from Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Ramification/GaloisValuation/RamificationQuotients.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/GaloisValuation/RamificationQuotients.lean#L28-L44),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. The structure is at
lines 30–36 and the instance at lines 43–44. The complete original file
has SHA-256
`40eb7a06cadc92dae7ce70173072c83b60b114a8ccc3559fb003b9223d1330a8`.

The registered source is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
at `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the source
path above. The attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum was present in the workspace, project or supplied
Library errata lookup. The public declaration partition identifies this
file as M224 and records no patch10 change.

## Interface and meaning

The complete structure interface, with namespace
`Langlands.NYLL.RamificationTheory.DiscreteValuationField` open, is:

```lean
structure AntitoneNormalSubgroupFiltration (G : Type u) [Group G] where
  lower : ℕ → Subgroup G
  lower_normal : ∀ n : ℕ, (lower n).Normal
  antitone : ∀ {m n : ℕ}, m ≤ n → lower n ≤ lower m
```

Here `u` is arbitrary and the structure belongs to `Type u`. The group
type `G` is explicit and its `Group G` instance is supplied. These are
the only structure parameters.

The field `lower` supplies a subgroup of `G` at each natural index,
including zero. The field `lower_normal` certifies that each term is a
normal subgroup of this same ambient group. Its index `n` is explicit.
The field `antitone` states subgroup inclusion in the decreasing
direction: from `m ≤ n`, it gives `lower n ≤ lower m`. Both indices
`m` and `n` are implicit. Subgroup order and normality are the ordinary
Mathlib notions; no new subgroup carrier or group law is introduced.

The instance has this complete interface and body, with the structure's
namespace also open:

```lean
instance lower_normal_instance
    {G : Type u} [Group G] (F : AntitoneNormalSubgroupFiltration G)
    (n : ℕ) : (F.lower n).Normal :=
  F.lower_normal n
```

It exposes the stored normality proof to typeclass search. The group
type is implicit, the group instance is supplied, and `F` and `n` are
explicit. The implemented proof is precisely the normality projection
at `n`; it does not establish a new arithmetic normality theorem.

The bundle records data and laws for an arbitrary group. In particular,
it adds no finite-group, valued-field, action, completeness, termination
or separatedness hypothesis. It does not require the filtration to
start at the whole group or eventually reach the trivial subgroup.
The name's `DiscreteValuationField` namespace is inherited from the
source and contributes no field or valuation parameter.

## Exact declaration map and modifications

Write `S` for the original namespace
`RamificationTheory.DiscreteValuationField` and `T` for
`Langlands.NYLL.RamificationTheory.DiscreteValuationField`. The following
table uses these namespace abbreviations only to display the exact map:

| Source declaration | Adapted declaration |
| --- | --- |
| `S.AntitoneNormalSubgroupFiltration` (M224.001) | `T.AntitoneNormalSubgroupFiltration` |
| `S.AntitoneNormalSubgroupFiltration.lower_normal_instance` (M224.002) | `T.AntitoneNormalSubgroupFiltration.lower_normal_instance` |
| `S.AntitoneNormalSubgroupFiltration.mk` | `T.AntitoneNormalSubgroupFiltration.mk` |
| `S.AntitoneNormalSubgroupFiltration.lower` | `T.AntitoneNormalSubgroupFiltration.lower` |
| `S.AntitoneNormalSubgroupFiltration.lower_normal` | `T.AntitoneNormalSubgroupFiltration.lower_normal` |
| `S.AntitoneNormalSubgroupFiltration.antitone` | `T.AntitoneNormalSubgroupFiltration.antitone` |

All other declarations automatically generated for the structure use
the same prefix replacement. Their generation is delegated to the
approved Lean compiler; there are no additional hand-written
declarations.

The original field types, index types, explicit and implicit binders,
and instance body are preserved. The namespace gains `Langlands.NYLL`.
The original import `Mathlib.GroupTheory.QuotientGroup.Finite` is
replaced by `Mathlib.Algebra.Group.Subgroup.Defs`, which already supplies
the subgroup order and normality predicate needed here. The unused
universe `v` and unnecessary `noncomputable section` are omitted.
The module documentation describes this extracted unit; the structure
and field documentation retain their source meaning.

The existing `Langlands.Ramification.congruenceGroup` and `lowerGroup`
construct concrete subgroups from a supplied action on a local ring.
They do not provide this arbitrary-group bundle with these fields.
Mathlib's `FiniteIndexNormalSubgroup` additionally requires finite
index, so it cannot replace this interface. This module reuses
Mathlib's existing `Subgroup`, subgroup inclusion and `Subgroup.Normal`.

Only the structure, its compiler-generated declarations and its
normality instance are included. Quotient, subquotient, inertia and
wild-inertia aliases and the later source theorem commands are
separate units. No arithmetic filtration is constructed here.
The later M305 arithmetic value must use the published actual
lower-group normality and antitonicity proofs when filling these
fields. Herbrand functions and inertia or reciprocity conclusions
remain separate work.

## Attribution

The original copyright and author header is retained verbatim:
Copyright (c) 2026 Naganori Yamaguchi
(`https://github.com/n-yamaguchi-0729`), all rights reserved;
authors: Naganori Yamaguchi (assisted by OpenAI Codex).
The source is released under Apache-2.0. The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are byte-identical
to the pinned originals. Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The source file has no entry in the root NOTICE's third-party path
inventory; the inherited notices and earlier-source credits remain
preserved there.

Worker 106 supplied the source extraction and exact field and normality
projection analysis in the task contract. Worker 60 independently
checked the original source and reuse candidates, implemented this
focused extraction, reduced the import and wrote this documentation
on 1 November 2026. The Lean header records the modifications.
