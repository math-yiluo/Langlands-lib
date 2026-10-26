# Henselian discrete valuation fields and residue data

This module adapts precisely M104.007–011, lines 190–216 of Naganori
Yamaguchi's
[`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Henselian.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Henselian.lean#L190-L216),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The original file has SHA-256
`cce4a6ecfed6076732a5041ad23935a638de6eb5c3c35287d289c8b1717e0cf2`.
The source header, imports, namespace and universe context, and the selected
declarations through line 216 were read directly.

The original is retained under the registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
in `n-yamaguchi-0729--ClassFieldTheory/source/`.
Its attribution supplement is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No errata directory was present at the workspace, project or current
Library `notes/errata` lookup. This source has no modification in the
recorded patch10.

## Bundle and supplied Henselianity

All adapted names below are relative to
`Langlands.NYLL.ValuationTheory.DiscreteValuationField`.
For a field `K : Type u` with supplied `[Field K]`, the structure
`HenselianDVF.{u, v} K` extends the published `DVF.{u, v} K`.
The universes `u` and `v` are independent. The parent retains its chosen
value group in `Type v`, its `LinearOrderedCommGroupWithZero` structure,
its actual Mathlib valuation of `K`, and its proof of rank-one discreteness.
As in `DVF`, discreteness concerns the valuation's value subgroup; it does
not assert surjectivity onto the chosen ambient value group.

The structure has the following parent projection and one added field.

| Projection, relative to `HenselianDVF` | Type and meaning |
| --- | --- |
| `toDVF F` | The underlying `DVF.{u, v} K`, with its existing chosen data. |
| `instHenselian F` | `HenselianRing F.toDVF.valuationSubring F.toDVF.maximalIdeal`. |

The added field uses the root Mathlib class `HenselianRing` from
`Mathlib.RingTheory.Henselian`. For a commutative ring `R` and ideal `I`,
this Prop-valued class stores `I ≤ Ideal.jacobson ⊥` and lifting of a
simple root modulo `I` for a monic polynomial: if `f.eval a₀ ∈ I` and
the residue of `f.derivative.eval a₀` is a unit, then there is a root
`a : R` with `a - a₀ ∈ I`. Here `R` is the actual valuation subring and
`I` is its canonical local-ring maximal ideal.

`HenselianDVF.instHenselian` retains its source `[instance]` attribute.
It exposes the Henselianity proof stored in the supplied bundle.
The parent `DVF.instValueGroup` and `DVF.instRankOneDiscrete` remain the
existing instance projections for the inherited data. Canonical Mathlib
instances supply the valuation ring's commutative-ring, local-ring and
domain structures, and the residue field's field structure.
This module adds no wrappers for those instances.

The constructor requires a chosen discrete valuation together with the
displayed Henselianity proof. Defining this structure proves no
Henselianity or existence assertion for arbitrary discrete valuation
fields. The constructor, recursors and generated projections are intrinsic
parts of the structure definition.

## Canonical residue data

In this table the names are relative to `HenselianDVF`, and
`F : HenselianDVF.{u, v} K`.

| Declaration | Type | Body |
| --- | --- | --- |
| `valuationSubring F` | `Type u` | `F.toDVF.valuationSubring` |
| `maximalIdeal F` | `Ideal F.valuationSubring` | `F.toDVF.maximalIdeal` |
| `residueField F` | `Type u` | `F.toDVF.residueField` |
| `residueMap F` | `RingHom F.valuationSubring F.residueField` | `F.toDVF.residueMap` |

All four declarations are reducible `abbrev`s with the same bodies as
the source. Unfolding the parent abbreviations identifies the first with
the type underlying `F.toDVF.valuation.valuationSubring`, whose elements
are `x : K` with valuation at most one. The maximal ideal is
`IsLocalRing.maximalIdeal F.valuationSubring`, the residue field is
`IsLocalRing.ResidueField F.valuationSubring`, and the map is
`IsLocalRing.residue F.valuationSubring`. Thus the residue field is the
actual quotient by the maximal ideal, and the map is the canonical
quotient homomorphism. No alternative ideal, quotient or map is chosen.
Both the valuation ring and residue field retain the field universe `u`.

## Exact source correspondence and imports

Write `S = ValuationTheory.DiscreteValuationField` for the original
namespace and `T = Langlands.NYLL.ValuationTheory.DiscreteValuationField`
for the adapted namespace.

| Original declaration and starting line | Adapted declaration |
| --- | --- |
| `S.HenselianDVF`, line 191, M104.007 | `T.HenselianDVF`; extends the same chosen `DVF.{u, v} K` and adds exactly the same `instHenselian` field. |
| `S.HenselianDVF.instHenselian`, line 193 | `T.HenselianDVF.instHenselian`; source instance attribute from line 195 retained. |
| `S.HenselianDVF.valuationSubring`, line 202, M104.008 | `T.HenselianDVF.valuationSubring`; unchanged type and body through the parent. |
| `S.HenselianDVF.maximalIdeal`, line 206, M104.009 | `T.HenselianDVF.maximalIdeal`; unchanged type and body through the parent. |
| `S.HenselianDVF.residueField`, line 210, M104.010 | `T.HenselianDVF.residueField`; unchanged type and body through the parent. |
| `S.HenselianDVF.residueMap`, line 214, M104.011 | `T.HenselianDVF.residueMap`; unchanged ring-homomorphism type and body through the parent. |

The two imports are
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic`
and `Mathlib.RingTheory.Henselian`. The first replaces the original
`Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic` import
and supplies the already-published chosen valuation bundle and canonical
residue data. The Mathlib import is unchanged. No earlier idempotent
theorem is needed for these declarations, and no external NYLL module
closure is imported.

Only M104.007–011 is extracted. The earlier idempotent-lifting results,
later polynomial-lifting, DVR, maximal-ideal and root-lifting theorems,
complete-to-Henselian or complete-to-DVF projections, completeness and
extension-existence claims, and comparisons to a host valuation are
outside this module.

## Attribution and modifications

The original copyright and author header is retained verbatim:
copyright 2026 Naganori Yamaguchi
(`https://github.com/n-yamaguchi-0729`), all rights reserved;
authors Naganori Yamaguchi (assisted by OpenAI Codex).
The source is released under Apache-2.0. Unmodified copies of its
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are already published
and reused. Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The selected `DiscreteValuationField/Henselian.lean` has no source-specific
entry in the retained NOTICE or the ValuedFieldTheory third-party
attribution table.

Worker 54 extracted the selected declarations, added the
`Langlands.NYLL` namespace prefix, changed the Basic import to the
published module, clarified the abbreviation docstrings, and wrote this
source map and scope documentation on 26 October 2026.
The Lean header records these modifications. No compatibility proof
patch or another worker's implementation is used.
