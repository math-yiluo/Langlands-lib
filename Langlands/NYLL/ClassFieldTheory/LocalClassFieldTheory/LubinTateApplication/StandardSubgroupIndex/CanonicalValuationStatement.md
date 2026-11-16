# Canonical inverse-uniformizer valuation target (M377.002)

`Langlands.NYLL.LubinTate.standardLubinTateCanonicalBaseUniformizerUnit_inv_valuationMapStatement`
is a Prop-valued definition packaging the assertion of source theorem M377.002.
Its complete proposition, inside `namespace Langlands.NYLL.LubinTate` with
`open LocalFieldTheory.IsNonarchimedeanLocalField`, is:

```lean
(K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

valuationMap K
    (Additive.ofMul
      (standardLubinTateBaseUniformizerUnit
        (standardLocalFieldUniformizer_isUniformizer K))⁻¹) =
  1
```

The explicit field `K` is in Type 0. The four ordered instances are the
supplied field structure, valuative relation, topology and Mathlib
nonarchimedean local-field certificate. There is no additional parameter.
The equality states that the inverse of the actual canonical packaged
Lubin–Tate uniformizer, viewed as a field unit and then in `Additive Kˣ`,
has normalized additive valuation `1`. The inversion precedes
`Additive.ofMul`, exactly as in the source. The source valuation convention
is retained without a sign change.

## Published dependencies and canonical package

The three direct imports are:

- `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.UniformizerProof`,
  supplying the actual theorem
  `Langlands.NYLL.LubinTate.standardLocalFieldUniformizer_isUniformizer K`
  (M335.021), together with the canonical `standardLocalField K` and
  `standardLocalFieldUniformizer K` through its published imports.
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.NormSubgroup.BaseUniformizerUnit.Definitions`,
  supplying
  `Langlands.NYLL.LubinTate.standardLubinTateBaseUniformizerUnit`
  (M374.002).
- `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.Definitions`,
  supplying
  `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap`
  (M134.002), built from `valuationUnitsMulHom` (M134.001).

The uniformizer theorem certifies the canonical integer-ring element as a
uniformizer for `(standardLocalField K).valuation`. The unit constructor
uses that very proof to infer the local-field package and the element, and
constructs the field unit by `Units.mk0`. Thus the target retains the
actual canonical package; it introduces no replacement element or
uniformizer-proof hypothesis. The valuation map is the published
`Additive Kˣ →+ Int` from the supplied valuative relation and its canonical
integer value-group normalization. These dependencies are imported by
their Lean module names and are unmodified.

## Original source and exact locations

The original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/LubinTateApplication/StandardSubgroupIndex.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/LubinTateApplication/StandardSubgroupIndex.lean#L55-L65)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The source unit is M377.002,
`LubinTate.standardLubinTateCanonicalBaseUniformizerUnit_inv_valuationMap`.
Its docstring is at lines 55–56, theorem declaration and complete equality
at lines 57–62, and proof at lines 63–65 (following `:= by` on line 62).
The complete section telescope is at lines 42–43; the namespace and opens
are at lines 34–40. The original file SHA-256 is
`09a3021fc016de44aa5717a06d80cfa849c2ec642f9301a93538f1bb184e42b8`.
The header, imports, section context and relevant source declarations were
read directly from the pinned local snapshot.

The registered source is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The pinned source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
No matching project erratum was found, and the public compatibility
inventory records no patch10 change to this source module.

## Complete adaptation and scope

Worker 212 made the following modifications on 16 November 2026:

- Extracted only M377.002's assertion and retained its original docstring.
- Prefixed `LubinTate` with `Langlands.NYLL` and appended `Statement`
  to the declaration name.
- Replaced the theorem command and proof by `def ... : Prop :=`,
  with the original equality as its body.
- Replaced the six original imports (`Mathlib.GroupTheory.Index`,
  `Mathlib.SetTheory.Cardinal.Finite`, and the source modules
  `StandardLocalField`, `UniformizerPrincipalQuotient`, `FiniteParameters`
  and `NormSubgroup`) with the three focused published imports listed above.
- Kept only `open LocalFieldTheory.IsNonarchimedeanLocalField`;
  omitted the repeated `open LocalFieldTheory`, the unused
  `DiscreteValuationField` and `CompleteDVF` opens, `open scoped ValuativeRel`,
  and the unused outer `noncomputable section`.
- Omitted the original whole-file module documentation and all other source
  units, and added the prominent modification record and this paired Markdown.

The original explicit `K : Type`, instance order and equality are unchanged
apart from namespace resolution and formatting. This module defines the
proposition; it does not prove it. The preceding M377.001 equality and the
source proof's `valuationMap_apply` and
`v_inverseIntegerRingUniformizerFieldUnit` are not required to state it and
are not reproduced. No global instance or other declaration is introduced.

## Attribution and license

The original copyright, Apache-2.0 release line and author header are
retained verbatim: copyright 2026 Naganori Yamaguchi; authors Naganori
Yamaguchi (assisted by OpenAI Codex). The existing unmodified
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) remain in `licenses/NYLL/`.
They match the pinned originals byte for byte; their SHA-256 values are
respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The upstream repository is read as a source snapshot and is not installed.
