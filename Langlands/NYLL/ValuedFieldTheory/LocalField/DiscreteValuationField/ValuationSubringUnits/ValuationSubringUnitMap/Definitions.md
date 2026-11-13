# Valuation-subring units inside field units

This module extracts exactly M388.001, lines 31–34, from Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/ValuationSubringUnits/ValuationSubringUnitMap.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/ValuationSubringUnits/ValuationSubringUnitMap.lean#L31-L34),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The complete original
file, including its header, import, namespace and universe context, was read.
Its SHA-256 is
`13e51b4e4cae7b9132808332f696efef9d971020781da19ca56c93249cf32084`.

The readable pinned source is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`,
registered as `external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The associated attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No NYLL or Yamaguchi erratum was found in the checked Library and project
`notes/errata` filenames.

## Declaration and meaning

The sole authored declaration is
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.valuationSubringUnitsToFieldUnits`.
Its full type is

```lean
{K : Type u} → [Field K] →
  (F : Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K) →
  F.valuationSubringˣ →* Kˣ
```

The universes `u` and `v` are independent. The field and its field structure
are implicit parameters; the chosen complete discrete valuation bundle `F`
is explicit. The declaration's `LocalFieldTheory` namespace follows the
source, while its argument type is the published `ValuationTheory` bundle.

For `A = F.valuation.valuationSubring`, the published abbreviation
`F.valuationSubring` is definitionally the type underlying `A`. Thus
`F.valuationSubringˣ` is the group of units of the actual chosen valuation
subring, and `Kˣ` is the group of units of the underlying field. The map is
exactly the source expression:

```lean
F.valuation.valuationSubring.unitGroup.subtype.comp
  F.valuation.valuationSubring.unitGroupMulEquiv.symm.toMonoidHom
```

Mathlib's `ValuationSubring.unitGroup A` is a subgroup of `Kˣ`, consisting
of the field units with valuation one for the valuation associated to `A`.
The multiplicative equivalence
`ValuationSubring.unitGroupMulEquiv A : A.unitGroup ≃* Aˣ` identifies this
subgroup with the units of `A`. Its inverse first regards a unit of `A`
as an element of `A.unitGroup`; the subgroup's `subtype` homomorphism then
includes that element in `Kˣ`. The composition therefore sends a
valuation-subring unit to the field unit with the same underlying value
and inverse. It retains the subring of `F.valuation` throughout.

The multiplicative laws are supplied by these existing homomorphisms and
their composition. This module adds the definition alone. The source's
evaluation theorem M388.002 and membership theorem M388.003, and all
further statements and theorems, are outside this extraction.

## Source correspondence and reused declarations

| Original source | Adapted declaration |
| --- | --- |
| `LocalFieldTheory.DiscreteValuationField.CompleteDVF.valuationSubringUnitsToFieldUnits`, M388.001, lines 31–34 | `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.valuationSubringUnitsToFieldUnits`; same independent universes, field parameter, bundle argument, result and body. |

The single import is
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Projections`.
It supplies the published
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF.valuationSubring`
abbreviation and imports
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Definitions`,
which supplies `CompleteDVF`, its `valuation` projection, and the stored
value-group and complete-discrete instances. The subring abbreviation
unfolds through the published `CompleteDVF.toHenselianDVF`,
`HenselianDVF.valuationSubring`, and `DVF.valuationSubring` to the chosen
valuation's Mathlib valuation subring.

The imported closure already supplies Mathlib's
`Valuation.valuationSubring`, `ValuationSubring.unitGroup`,
`ValuationSubring.unitGroupMulEquiv`, `Subgroup.subtype`,
`MulEquiv.symm`, `MulEquiv.toMonoidHom`, and `MonoidHom.comp`.
The canonical ring and unit-group instances are reused.
There is no new bundle, valuation, local instance or global instance.
The source import
`Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic`
is replaced by the focused published import above; its unrelated
declarations are unnecessary for this expression.

## Attribution and modifications

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi (`https://github.com/n-yamaguchi-0729`), all rights
reserved; authors Naganori Yamaguchi (assisted by OpenAI Codex).
The source is released under Apache-2.0. The already published
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are reused unchanged.
Their SHA-256 values were checked against the pinned originals:
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
respectively. The retained NOTICE contains no entry naming
`ValuationSubringUnitMap`.

On 13 November 2026, Worker 324 extracted this declaration and its
docstring, added the `Langlands.NYLL` namespace prefix, explicitly
qualified the existing `CompleteDVF` argument type, replaced the source
import as described above, and wrote this Markdown and the focused
module documentation. The definition body is unchanged. No compatibility
proof patch or another worker's draft implementation is used.
