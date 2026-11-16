# NYLL M300.005: fixed field of an abstract compositum

This module proves the published proposition
`Langlands.NYLL.LocalClassFieldTheory.finiteAbelianSubextension_compositum_fixedFieldStatement`
with the complete source telescope:

```lean
theorem finiteAbelianSubextension_compositum_fixedField
    (K : Type) [Field K]
    (U T : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    finiteAbelianSubextension_compositum_fixedFieldStatement K U T
```

The namespace is `Langlands.NYLL.LocalClassFieldTheory`, with
`open ClassFormation`. The field `K` remains in universe zero. The
arguments are the published finite abelian subextension packages over
`intrinsicAbstractBase K`, the closed subgroup fixing the bottom
intermediate field of `SeparableClosure K / K`. The exact conclusion is

```lean
abstractFixedField K (SeparableClosure K) (U.compositum T).field =
  abstractFixedField K (SeparableClosure K) U.field ⊔
    abstractFixedField K (SeparableClosure K) T.field
```

Here the supremum is in `IntermediateField K (SeparableClosure K)`: the
smallest intermediate field containing both fixed fields. The theorem has
no local-field, valuation, finite-dimensionality or supplied Galois premise.
Mathlib supplies the Galois instance for the separable closure. There are
no new definitions or instances in this module.

## Implemented proof

The proof follows source lines 133–144 after unfolding the proposition
target. Let `EU` and `ET` denote the two concrete fixed fields.

1. Apply `InfiniteGalois.fixedField_fixingSubgroup` in reverse to write
   `EU ⊔ ET` as the fixed field of its fixing subgroup. Congruence of
   `IntermediateField.fixedField` reduces the result to equality of
   the two subgroups.
2. The published `abstractFixedField` is an abbreviation for
   `IntermediateField.fixedField` of the underlying subgroup. The
   published `FiniteAbelianSubextension.compositum` has underlying
   subgroup `U.field ⊓ T.field`. Thus `change` reduces the left side
   to `U.field.toSubgroup ⊓ T.field.toSubgroup`.
3. `IntermediateField.fixingSubgroup_sup` expresses the fixing subgroup
   of `EU ⊔ ET` as the intersection of the fixing subgroups of `EU`
   and `ET`. Since `U.field` and `T.field` are closed, the two applications
   of `InfiniteGalois.fixingSubgroup_fixedField` identify these with
   `U.field.toSubgroup` and `T.field.toSubgroup`, closing the equality.

The single import is the published target module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding.CompositumFixedField.Statements`.
It supplies the published M296 compositum, M091 intrinsic base, M099
abstract fixed field and Mathlib infinite Galois correspondence. The proof
uses none of the preceding M300 norm-transport or abelian-Galois results.
All constructions and facts are reused by their Lean names.

## Provenance and modifications

Worker 667 adapts Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean#L126-L144),
M300.005, type lines 128–132 and proof lines 133–144, with section binders
at lines 25–32. The source file's SHA-256 is
`8e132aed14beed67586f530d41fc5afa35a302c78c2a13c3d71c1f45da3eb4d3`.
The retained source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collections are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No NYLL erratum is recorded in the current Library's errata notes.

| Unit | Source declaration | Published proof declaration |
| --- | --- | --- |
| M300.005 | `LocalClassFieldTheory.finiteAbelianSubextension_compositum_fixedField` | `Langlands.NYLL.LocalClassFieldTheory.finiteAbelianSubextension_compositum_fixedField` |

The modifications are:

- Prefix the namespace with `Langlands.NYLL` and write the source section
  binders `(K : Type) [Field K]` explicitly on the theorem. Preserve their
  order, binder kinds and universe-zero scope, as well as the explicit
  arguments `U T`.
- State the theorem against the published proposition target and unfold
  that target before the unchanged source proof.
- Replace the broad source imports with the published target module and
  omit all other source declarations. Retain `noncomputable section` and
  the used `ClassFormation` opening; drop the unused `LocalFieldTheory`,
  `RamificationTheory`, `CyclicCohomology` and `KummerTheory` openings.
- Replace the whole-file overview with focused documentation and an
  explicit modification record; keep the source theorem's docstring.

The original copyright and author header is retained. The existing
Apache-2.0 `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are unchanged;
their SHA-256 values are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
This is an adaptation of the pinned original proof. No other worker's
draft or compatibility patch was reused.

## Development verification

In approved environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`),
development check `db87e5a9-2064-428c-ab80-313eb649325d` completed a Lake
build of this theorem module with zero errors and warnings. Declaration
inspection reported a theorem with no universe parameters and only
`propext`, `Classical.choice` and `Quot.sound` as axioms. Formal candidate
validation, independent semantic review and Library integration remain
separate requirements.
