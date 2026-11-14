# The fixed field of a finite abelian subextension is abelian: proposition target

This module defines one Prop-valued definition in
`namespace Langlands.NYLL.LocalClassFieldTheory`, with `open ClassFormation`:

```lean
def finiteAbelianSubextension_fixedField_isAbelianGaloisStatement
    (K : Type) [Field K]
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) : Prop :=
  IsAbelianGalois K
    (abstractFixedField K (SeparableClosure K) L.field)
```

## Meaning

Let `K` be a field in `Type` (universe zero), let `Ω = SeparableClosure K` be
Mathlib's chosen separable closure and let `G_K = Gal(Ω/K)`, which is
`intrinsicAbsoluteGalois K`. The closed subgroup `intrinsicAbstractBase K` is
the fixing subgroup of the bottom intermediate field `⊥ : IntermediateField K Ω`.
An argument `L : FiniteAbelianSubextension (intrinsicAbstractBase K)` is an
actual finite abelian subextension package over that subgroup: a closed
subgroup `L.field` of `G_K` contained in `intrinsicAbstractBase K`, normal in
it with finite and commutative quotient (the published M296 structure).

`abstractFixedField K Ω L.field` is the concrete intermediate field
`IntermediateField.fixedField L.field.toSubgroup` of `Ω / K`, the elements of
the separable closure fixed by every automorphism in `L.field`. The target
says that this field, as an extension of `K` with the algebra structure of an
intermediate field, satisfies Mathlib's `IsAbelianGalois`: it is Galois over
`K` and its automorphism group `Gal(E/K)` is commutative.

The conclusion is exactly `IsAbelianGalois`, as in the source. Finite
dimensionality of the fixed field over `K` is not part of the stated
conclusion (the source docstring's word "finite" describes the package, and
the source proof establishes `FiniteDimensional` only as a local
instance). No valuation, topology, local-field or finite-dimensionality
hypothesis is placed on `K`. This is a proposition definition; no proof is
asserted.

## Source

The original is Naganori Yamaguchi's NYLL `ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean#L83-L90),
lines 83–90 (docstring 83–86, type 87–90; the proof, lines 91–124, is
omitted). The whole source file was read; its SHA-256 is
`8e132aed14beed67586f530d41fc5afa35a302c78c2a13c3d71c1f45da3eb4d3`.

| Unit | Source declaration | Adapted declaration |
| --- | --- | --- |
| M300.004 | theorem `LocalClassFieldTheory.finiteAbelianSubextension_fixedField_isAbelianGalois` | `Langlands.NYLL.LocalClassFieldTheory.finiteAbelianSubextension_fixedField_isAbelianGaloisStatement` |

The source context, lines 25–32, is `noncomputable section`,
`namespace LocalClassFieldTheory`,
`open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory`,
`open ClassFormation` and `variable (K : Type) [Field K]`; the file declares no
`universe`. The source theorem mentions `K`, so its complete telescope is
`(K : Type) [Field K] (L : FiniteAbelianSubextension (intrinsicAbstractBase K))`,
with `K` and `L` explicit.

Every source name used in the type resolves to a published Library
declaration with the same body, which is reused by Lean name:

| Source declaration | Published declaration (unit) | Module |
| --- | --- | --- |
| `ClassFormation.FiniteAbelianSubextension`, `.field` | `Langlands.NYLL.ClassFormation.FiniteAbelianSubextension`, `.field` (M296.001–.002) | `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension.Definitions` |
| `LocalClassFieldTheory.intrinsicAbstractBase` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbstractBase` (M091.003) | `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions` |
| `LocalClassFieldTheory.abstractFixedField` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField` (M099.001) | `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions` |
| `IsAbelianGalois`, `SeparableClosure` | the same Mathlib declarations (`_root_.IsAbelianGalois` from `Mathlib.FieldTheory.Galois.Abelian`) | — |

As recorded with M099.001, `abstractFixedField` does not use its section's
`[IsGalois k Ω]` variable, so no Galois instance on `SeparableClosure K` enters
this target. The source defines no `IsAbelianGalois`; it uses Mathlib's.

This is unit M300.004 of the published
[NYLL port partition](../../../../../../../../notes/reuse/nyll-public-port-plan.md)
(appendix row in `notes/reuse/nyll-public-port/m289-m312.md`, section M300).

## Modifications

Worker 451 made these modifications, and no others:

- The source theorem's type is extracted and closed over its complete
  telescope as a `def ... : Prop`; the name is prefixed with `Langlands.NYLL`
  and receives the suffix `Statement`. The section variables
  `(K : Type) [Field K]` become explicit leading binders, in the source order
  and with the source binder kinds.
- The source proof (lines 91–124) is omitted; it remains a separate proof
  obligation.
- The source imports (`Existence.LocalAbsoluteData`,
  `LocalReciprocity.IntrinsicAbsoluteData`, `LocalReciprocity.SeparableUnitsNorm`,
  `LocalReciprocity.TopologicalReciprocity` and
  `Mathlib.FieldTheory.Galois.Abelian`) are replaced by Mathlib's
  `FieldTheory.Galois.Abelian` and the three published modules
  `FiniteAbelianSubextension.Definitions`,
  `IntrinsicAbsoluteData.Initial.Definitions` and
  `FiniteAbstractFixedField.Initial.Definitions`, which supply every
  declaration used. The successful focused check below confirms that this
  import set suffices; the target needs neither the targets M300.001/.002, the
  norm subgroup M300.003, nor the source proof ingredients.
- The unused openings `LocalFieldTheory`, `RamificationTheory`,
  `CyclicCohomology` and `KummerTheory` are dropped; `ClassFormation` is kept.
- The docstring is the source docstring unchanged.

No equivalent Library or Mathlib declaration exists: a search of the Library
found `IsAbelianGalois` only for supplied extensions `L/K` (as hypotheses or
conclusions), never for fixed fields of the NYLL package
`FiniteAbelianSubextension`, and Mathlib has no such package. No local, scoped or global instance is introduced, and no other
worker's draft was reused.

The source was read from the retained snapshot under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`,
registered as `external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`), with the
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` (content
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No NYLL erratum is recorded in the Library's errata notes.

The original copyright and author header is retained. The Apache-2.0
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) in the Library are
unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Development checks

In the approved environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0, Mathlib `5ed2965256430c3649e86755f9576b54eca72435`), check
`a5bf44a9-62d4-428e-8018-f6afbcda2962` compiled this module with no errors or
warnings and inspected the declaration as a definition with
`statement_returns_prop: true` and no universe parameters. A private
diagnostic, check `e81dc906-609e-471d-8028-cdba7d188cb7`, printed the
declaration with full names and universes, showing the telescope
`(K : Type) → [Field.{0} K] → FiniteAbelianSubextension.{0} (intrinsicAbstractBase K) → Prop`
and the body `IsAbelianGalois.{0, 0} K ↥(abstractFixedField K (SeparableClosure.{0} K) L.field)`,
and confirmed by `rfl` that it equals the displayed body written with fully
qualified names (`_root_.IsAbelianGalois`,
`Langlands.NYLL.LocalClassFieldTheory.abstractFixedField`,
`Langlands.NYLL.ClassFormation.FiniteAbelianSubextension.field` and
`Langlands.NYLL.LocalClassFieldTheory.intrinsicAbstractBase`). The diagnostic
is not part of this contribution. Independent semantic acceptance and the
proof are separate obligations.
