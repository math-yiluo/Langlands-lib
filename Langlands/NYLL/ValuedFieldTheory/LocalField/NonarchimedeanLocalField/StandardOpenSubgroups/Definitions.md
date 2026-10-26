# Principal-unit subgroups of field units

This module defines `Langlands.NYLL.LocalFieldTheory.fieldPrincipalUnits`.
For an arbitrary field `K : Type u` with a supplied `ValuativeRel K`, put
`O = Valuation.integer (ValuativeRel.valuation K)`. For each natural number
`n`, it is the image of the published subgroup
`Langlands.NYLL.LocalFieldTheory.principalUnits K n : Subgroup Oˣ`
under the canonical homomorphism from `Oˣ` to `Kˣ`. The source subgroup uses
the actual valuation ring and its maximal-ideal powers.

With `open scoped ValuativeRel`, the complete interface is

```lean
fieldPrincipalUnits.{u} (K : Type u) [Field K] [ValuativeRel K] (n : Nat) :
  Subgroup Kˣ
```

The exact body is

```lean
(principalUnits K n).map (Units.map (algebraMap 𝒪[K] K).toMonoidHom)
```

Here `𝒪[K]` is the canonical Mathlib integer subring `O`. Its `algebraMap`
to `K` is its subtype ring homomorphism. `Units.map` induces the homomorphism
on units, and `Subgroup.map` forms the subgroup image. This is a data
definition using already supplied canonical operations; it requires no
additional existence theorem or choice of representatives.

The definition retains its single arbitrary universe and every natural index,
including zero. Its only instance parameters are `Field K` and
`ValuativeRel K`. In particular, it has no topology, local-field,
discrete-valuation, finite-residue-field, completeness or characteristic
assumption.

## Source and adaptation

The original is Naganori Yamaguchi's NYLL `ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/StandardOpenSubgroups.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/StandardOpenSubgroups.lean#L19-L34),
lines 19–34, with the declaration at lines 32–34. The complete source file
has SHA-256
`9cf6baf50519f650504762782a5aed12500479b911fc1ac4db9a138207097d7d`.
This is exactly the data unit M289.001 of the published declaration partition.

| Original | Adapted |
| --- | --- |
| `LocalFieldTheory.fieldPrincipalUnits` | `Langlands.NYLL.LocalFieldTheory.fieldPrincipalUnits` |
| `LocalFieldTheory.principalUnits` | Published `Langlands.NYLL.LocalFieldTheory.principalUnits` |
| `LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits K` | `Units.map (algebraMap 𝒪[K] K).toMonoidHom` |

The last row unfolds the original wrapper at
[`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean#L182-L184),
lines 182–184 (M128.016). That file has SHA-256
`c696d08952343a0f668340bac35e2485e74b52134b0e205a3a4dc0653f48d25e`.
The wrapper's complete source signature is
`(K : Type u) [Field K] [ValuativeRel K] : 𝒪[K]ˣ →* Kˣ`,
and its body is exactly the expression in the last row. The surrounding
namespace `IsNonarchimedeanLocalField` introduces no local-field instance
parameter. The source namespace and noncomputable section were read together
with the declaration.

The adaptation prefixes the namespace with `Langlands.NYLL`, spells `ℕ` as
`Nat`, unfolds the inclusion wrapper, and replaces the broad
`PrincipalUnitQuotients` source import by the published principal-unit
definition and focused Mathlib operations. The original docstring is retained;
the module documentation describes this single definition. The unused source
namespace openings are omitted. No source proof is modified, and neither
selected module has an applicable patch10 edit. No other worker's modified
implementation draft is reused.

The original is registered as `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original passages were read directly from the registered snapshot. No
applicable errata file for either source ID was present in the project notes
or the supplied Library.

The original copyright and author header is preserved. The unchanged upstream
Apache-2.0 [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are already in the Library;
their SHA-256 values match the original:
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
respectively. Neither selected original path occurs in the root NOTICE or
the supplied ValuedFieldTheory third-party attribution table. This module
copies no additional third-party implementation.

## Reuse and scope

The published integer-unit `principalUnits` is reused by its Lean name.
Mathlib's `ValuationSubring.principalUnitGroup` has a field-unit codomain but
uses a strict valuation inequality and has no natural filtration index. The
host `Langlands.PadicField.TopologicalData.unitFiltration` in
`Langlands.ClassFieldTheory.Local.Units` also forms an image of congruence
units, but its input is supplied p-adic field data and its source subgroup is
a reduction kernel. The host `principalUnits` in
`Langlands.HarmonicAnalysis.Conductor` instead uses the supplied discrete
valuation. These constructions do not directly provide the required
arbitrary `Field`/`ValuativeRel` signature and exact source-image body.

The only new public declaration is `fieldPrincipalUnits`. This unit does not
add an inclusion wrapper, global instance, membership or zero-step theorem,
injectivity or evaluation theorem, uniformizer subgroup, openness or
finite-index result. It makes no host inertia or reciprocity assertion.

## Focused development check

The approved Lean service successfully built this module with these direct
imports:

- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits.Definitions`
- `Mathlib.Algebra.Group.Subgroup.Map`
- `Mathlib.Algebra.Group.Units.Hom`

No NYLL `Basic`, `PrincipalUnitQuotients` or original `StandardOpenSubgroups`
module is imported. This reports the tested import list rather than a claim
that each direct import is indispensable.

Development check `60d68510-8ea3-419a-91d4-233de0a470f4`, in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), returned `ok: true` and
exit code zero. It built the definition and private diagnostics with zero
errors and one unused-variable warning in a private diagnostic. The complete
unapplied declaration was assigned to the displayed telescope and printed
with universe parameters and body. Inspection identified a definition with
exactly the universe parameter `u`, and only the standard assumptions
`propext`, `Classical.choice` and `Quot.sound`.

Private reflexivity checks also confirmed that the chosen `algebraMap` is
the canonical integer-subring subtype map and that `Units.map` has its
underlying field value. These private diagnostics are excluded from the
contribution. Development checks are separate from independent semantic
acceptance and publication.
