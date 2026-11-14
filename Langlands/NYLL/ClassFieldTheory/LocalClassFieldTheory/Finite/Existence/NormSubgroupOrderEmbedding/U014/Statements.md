# NYLL M300.014: native finite-abelian norm order reversal target

Worker 539, 14 November 2026.

## Source and attribution

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`,
file SHA-256
`8e132aed14beed67586f530d41fc5afa35a302c78c2a13c3d71c1f45da3eb4d3`.
The declaration is M300.014, lines 417–431; its asserted type is at
lines 417–421, its proof at lines 422–431, and the surrounding parameter
declarations at lines 32 and 333–334. The source docstring is lines 415–416.
The readable original is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

Registered source `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original copyright, Apache-2.0 license and author header are retained.
The Library files `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain
unchanged, with SHA-256 respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
No NYLL-specific erratum was found in the Library errata filenames.

## Name map and complete telescope

| Unit | Original declaration | Adapted proposition target |
| --- | --- | --- |
| M300.014 | `LocalClassFieldTheory.finiteAbelianSubextension_le_iff_normSubgroup_le` | `Langlands.NYLL.LocalClassFieldTheory.finiteAbelianSubextension_le_iff_normSubgroup_leStatement` |

The target has the following complete, ordered telescope:

```lean
(K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]
(L₁ L₂ : ClassFormation.FiniteAbelianSubextension (intrinsicAbstractBase K))
```

Here `ClassFormation` means `Langlands.NYLL.ClassFormation`, and the two
intrinsic/norm names mean the declarations in
`Langlands.NYLL.LocalClassFieldTheory`. `K`, `L₁` and `L₂` are explicit;
all four bracketed arguments are instance-implicit. The ground field is
`Type`, not `Type u`; no universe generalization is introduced. The target's
body is exactly

```lean
L₁ ≤ L₂ ↔ finiteAbelianNormSubgroup K L₂ ≤ finiteAbelianNormSubgroup K L₁
```

This module defines that proposition and supplies no proof of it. It adds
no reciprocity equivalence, order-reversal premise, norm identity, finite
dimensionality premise or Galois premise.

## Actual objects and reuse

`Langlands.NYLL.ClassFormation.FiniteAbelianSubextension` is the existing
finite abelian package over a closed subgroup. The source order M296.014,
`Langlands.NYLL.PortInternal.M296.d014`, expresses field inclusion by
reversed containment of the represented absolute Galois subgroups:
`L₁ ≤ L₂` unfolds to `L₂.field.toSubgroup ≤ L₁.field.toSubgroup`.
It is imported from
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Order`.
No order instance is introduced here.

The existing `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbstractBase K`
is the closed fixing subgroup of the bottom intermediate field of
`SeparableClosure K`. M300.003,
`Langlands.NYLL.LocalClassFieldTheory.finiteAbelianNormSubgroup K L`, is
literally
`Langlands.NYLL.LocalFieldTheory.localNormSubgroup K
  (Langlands.NYLL.LocalClassFieldTheory.abstractFixedField K (SeparableClosure K) L.field)`.
The latter subgroup is the range of the ordinary field norm on units.
Its definition is reused from
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding.Definitions`.
Mathlib's `Mathlib.NumberTheory.LocalField.Basic` supplies the original
`IsNonarchimedeanLocalField` class.

The Library search for `finiteAbelianNormSubgroup` and
`finiteAbelianSubextension_le_iff_normSubgroup_leStatement` found no existing
target at the task's initial Library base
`9d71020c4b80abb41dbf8102ded7d93202edf495`. The prerequisite tasks own the norm-subgroup and order definitions; this
unit does not duplicate their declarations. Both prerequisites are published
and present in the workspace at Library base
`4f4af6baed8c8e029e87c8303ea44c8f1d9f2f86`.

## Modifications

1. Prefix the source namespace `LocalClassFieldTheory` with `Langlands.NYLL`.
2. Replace the source theorem with a `Prop`-valued `def`, append `Statement`
   to its name, and omit the entire source proof.
3. Move the section parameters `(K : Type) [Field K]` and
   `[ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]`
   into the declaration, preserving their binder kinds and order before
   the explicit extension arguments. Qualify `FiniteAbelianSubextension`
   by `ClassFormation` rather than opening that namespace.
4. Replace the original five imports with the three focused imports above.
   Drop the unused namespace openings and the `noncomputable section`,
   since this proposition definition does not perform a construction.
   Retain the source theorem docstring, replace the module docstring, and
   add the modification record.
5. Extract only M300.014's proposition target. The ordinary open
   finite-index subgroup map and order embedding are outside this unit.

## Validation and later proof route

The focused Lean-service check on 14 November 2026, diagnostic
`7625fbaa-5663-4fbf-abf8-fea0b7b0cfff`, compiled the entry module in
approved environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` with zero
errors and zero warnings. Inspection identified the exact declaration as
a definition with no universe parameters and reported
`statement_returns_prop = true`. M300.003 from Task 6121
`9194bb32-e084-4c9a-b5d3-cb48a0df1b61` and M296.014 from Task 6076
`92604b84-038e-4d2b-bd45-7a6d1dfdc78d` are published prerequisites.
This development check verifies elaboration and the proposition-valued
result; independent semantic acceptance and Library integration are
separate requirements.

The source proof first instantiates abstract order reversal M298.029 with
`localHenselianValuation K`, `separableClosureUnits_isClassFormation K`
and `intrinsicFiniteAbstractBase K`. It then transports inclusions using
injectivity of the inverse base fixed-unit equivalence and M300.008.
Those proof prerequisites are not added as hypotheses of this target.
The source proof does not call M300.010–.013 or M300.015. The successful
focused check uses only the three imports listed above and requires none
of those units for this proposition target. It does not establish the
complete dependency closure of the later proof.
