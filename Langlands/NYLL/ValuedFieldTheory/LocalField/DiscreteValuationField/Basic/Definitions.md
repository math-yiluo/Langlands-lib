# Chosen local-field package and residue data

This module extracts exactly M334.001–005, lines 34–59 of Naganori
Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Basic.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/Basic.lean#L34-L59)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The source file's SHA-256 is
`69d3219d17ef6bef4204e02538d5a3f28ee63edb1bc1e0be2354bed4c739afe9`.
Its header, imports, universe and namespace context, selected declarations,
and following declarations through line 115 were read directly.

The original is available in the registered source
`external-lean-reuse-snapshots-2026-10-21`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`, with attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement`.
The project errata lookup contained no entry for this source.
The recorded patch10 does not change this source module.

## Structure and inherited interface

All names below are relative to
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`.
For independent universes `u v` and a field `K : Type u` with `[Field K]`,
`LocalField.{u, v} K` extends the published
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K`.
The generated parent projection is
`LocalField.toCompleteDVF : LocalField.{u, v} K →
Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K`.
The field and its field instance are implicit parameters of this projection.

The only added field is
`LocalField.residueFinite (F : LocalField.{u, v} K) :
Finite F.toCompleteDVF.residueField`.
It retains the source instance attribute, so the supplied residue-finiteness
proof is available to typeclass inference, including at the definitionally
equal type `Finite F.residueField`. The structure packages supplied data
and proofs; it does not construct a local field from an arbitrary field.

The inherited interface retains the chosen `ValueGroup : Type v`,
its `LinearOrderedCommGroupWithZero` instance, the actual
`valuation : _root_.Valuation K F.ValueGroup`, and the stored
complete-discrete predicate, through the unchanged `CompleteDVF` parent.
The generated inherited projections and the published parent instance
attributes remain usable. In particular, the field universe and value-group
universe remain independent.

## Exact source correspondence

Write `S = LocalFieldTheory.DiscreteValuationField` for the original
namespace and `T = Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`
for the adapted namespace.

| Source unit and declaration | Adapted declaration | Type and body |
| --- | --- | --- |
| M334.001, `S.LocalField`, line 34 | `T.LocalField` | The structure extending the published `CompleteDVF.{u, v} K` with the single field above. |
| Field of M334.001, `S.LocalField.residueFinite`, line 36; instance attribute at line 38 | `T.LocalField.residueFinite` | `Finite F.toCompleteDVF.residueField`; the field binder and instance attribute are unchanged. |
| M334.002, `S.LocalField.residueField`, lines 45–46 | `T.LocalField.residueField` | `Type u := F.toCompleteDVF.residueField`. |
| M334.003, `S.LocalField.valuationSubring`, lines 49–50 | `T.LocalField.valuationSubring` | `Type u := F.toCompleteDVF.valuationSubring`. |
| M334.004, `S.LocalField.maximalIdeal`, lines 53–54 | `T.LocalField.maximalIdeal` | `Ideal F.valuationSubring := F.toCompleteDVF.maximalIdeal`. |
| M334.005, `S.LocalField.residueMap`, lines 57–59 | `T.LocalField.residueMap` | `RingHom F.valuationSubring F.residueField := F.toCompleteDVF.residueMap`. |

Each accessor has implicit `{K : Type u} [Field K]` and explicit
`(F : LocalField.{u, v} K)`. All four are reducible abbreviations with
the original types, bodies, order and docstrings. Ordinary structure
constructors, recursors and generated projections accompany `LocalField`.

The valuation subring is the type underlying the actual valuation subring
of the chosen valuation. The maximal ideal, residue field and residue map
are the canonical local-ring ideal, quotient field and quotient
homomorphism supplied by the published `CompleteDVF` projections. No
alternative residue data are chosen.

## Import and scope

The sole import is
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Projections`.
It supplies the published structure, its residue-data abbreviations and
their structural imports. The upstream full `Complete` module and eight
characteristic, rational, perfect-field, local-field, p-adic and integrality
imports are replaced by this focused import.

Only the five listed source units are extracted. There are no new
theorems or proposition targets. The later DVR, Henselian, uniformizer,
residue-characteristic and local-field classification results are outside
this unit.

## Attribution and complete modification record

The original 2026 copyright, Apache-2.0 release line and author header are
retained verbatim. The existing unmodified
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused. Their SHA-256
values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The retained NOTICE has no source-specific entry for this source file.

Worker 320 made these modifications on 13 November 2026:

- extracted M334.001–005 and their declaration docstrings into this focused
  module, omitting all later source declarations;
- prefixed both the declaration namespace and the opened valuation
  namespace with `Langlands.NYLL`;
- replaced the nine upstream imports by the one published import above;
- removed the unused universe variables `w x`, retaining independent `u v`;
- replaced the module documentation, added the prominent modification
  notice in the Lean header, and wrote this paired Markdown.

No declaration body, mathematical type, structure field, instance
attribute or proof is changed beyond qualification of names to the
published namespace. No compatibility patch is needed.
