# Field principal-unit comparison for the standard local field (M335.017)

This module proves
`Langlands.NYLL.LubinTate.standardLocalFieldHigherPrincipalUnitGroup_map_eq_fieldPrincipalUnitsStatement K n`
under the theorem name
`Langlands.NYLL.LubinTate.standardLocalFieldHigherPrincipalUnitGroup_map_eq_fieldPrincipalUnits`.
It imports the existing `StandardLocalField.PrincipalUnitComparisonStatements`
module and the proof in `StandardLocalField.HigherPrincipalUnitsComparisonProof`.
The target and all imported Lean/Markdown pairs are preserved.

The theorem retains the complete source telescope in its original order:

```lean
(K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (n : ℕ)
```

Both `K` and `n` are explicit. The field is in universe zero; no universe
generalization or additional hypothesis is introduced. The declared type is
the fully applied imported target, whose body is

```lean
(higherPrincipalUnitGroup
    (standardLocalField K).toCompleteDVF n).map
    (standardLocalFieldValuationUnitsToFieldUnits K) =
  Langlands.NYLL.LocalFieldTheory.fieldPrincipalUnits K n
```

This is an equality of subgroups of `Kˣ`, valid for every natural number
`n`, including zero.

## Implemented proof

After unfolding the target definition, the proof follows the original source:

1. Use `change` to expose the definitions of the two maps. The packaged
   valuation-unit inclusion is the composite of the inverse canonical
   integer-unit equivalence with `integerUnitsToFieldUnits K`. The right-hand
   side is the image of `principalUnits K n` under that latter inclusion.
   The published `fieldPrincipalUnits` definition uses
   `Units.map (algebraMap 𝒪[K] K).toMonoidHom`, which is definitionally
   `integerUnitsToFieldUnits K`.
2. Rewrite with `← Subgroup.map_map` to express the left-hand side as two
   successive subgroup images.
3. Rewrite the inner image using the imported theorem
   `Langlands.NYLL.LubinTate.standardLocalFieldHigherPrincipalUnitGroup_map_eq_principalUnits`
   (M335.014). Both remaining sides are the image of `principalUnits K n`
   under `integerUnitsToFieldUnits K`.

No local helper declarations are needed. M335.014 is used as a proved theorem;
it is not an additional assumption. The separate valuation-unit coercion
comparison M335.016 is not needed for this proof.

## Source and attribution

The original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean#L246-L261),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
Source unit M335.017 has its docstring at lines 246–247, statement at
lines 248–253 and proof at lines 254–261. The section variables are at
lines 37–38 and the original header at lines 1–5. The full source file's
SHA-256 is
`88a5745b57cab3c3b2241d6ce5344b5f9e0ad214e200e77072e4ad6fdc1a217e`.

The pinned source is available in the registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`. Its attribution
supplement is `nyll-classfieldtheory-fbd320cd-supplement`, content
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The project errata notes contain no entry for either registered source.

The original copyright, Apache-2.0 release line and author header are
retained verbatim. The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are preserved, with
respective SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

Worker 319 made these modifications on 16 November 2026:

- extracted only M335.017 and its docstring into the focused
  `FieldPrincipalUnitsComparisonProof` module;
- changed the namespace from `LubinTate` to `Langlands.NYLL.LubinTate`;
- replaced the six source imports by the two focused published imports
  listed above;
- expressed the theorem's type as the fully applied imported target and
  added its initial unfolding, retaining the original `change` and
  `rw` proof steps;
- retained `noncomputable section`, `open scoped ValuativeRel`, all four
  namespace opens and the exact section variables;
- replaced the module documentation, added the modification notice and
  wrote this paired Markdown.

All NYLL names in the proof resolve to their published `Langlands.NYLL`
adaptations. The target module itself is unchanged.
