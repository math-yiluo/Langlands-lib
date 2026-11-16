# Valuation of the canonical local-field package (M335.003)

This module proves
`Langlands.NYLL.LubinTate.standardLocalField_valuation_eqStatement K`
under the theorem name
`Langlands.NYLL.LubinTate.standardLocalField_valuation_eq`.
It imports the existing `StandardLocalField.Statements` module. The
target and all its imported Lean/Markdown pairs are preserved.

The theorem retains exactly the source telescope, in its original order:

```lean
(K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
```

In particular, `K` is explicit and in universe zero; no universe
generalization or extra hypothesis is introduced. Its declared type is
the fully applied published target, whose body is

```lean
(standardLocalField K).valuation = ValuativeRel.valuation K
```

The value group and its ordered structures on the left reduce to those
of `ValuativeRel.ValueGroupWithZero K`, so this is an equality of
valuations in the same type.

## Implemented proof

The proof first unfolds `standardLocalField_valuation_eqStatement` to
expose the equality. It then follows the source proof:

1. Unfold `standardLocalField`, whose parent complete DVF is
   `Langlands.NYLL.LocalFieldTheory.localCompleteDVF K`.
2. Unfold `localCompleteDVF`, the published canonical complete-DVF
   construction using the valued structure of the given valuative relation
   and the uniformity induced by the field topology.
3. Unfold
   `Langlands.NYLL.ValuationTheory.Valuations.completeDVFOfCompleteValuedField`.
   Its valuation field is `Valued.v`, which in this canonical construction
   reduces to `ValuativeRel.valuation K`.
4. Close the resulting definitional equality with `rfl`.

The proof introduces no helper declarations and uses no additional
comparison theorem. Only the required proof and this explanation are
added.

## Source and attribution

The original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean#L56-L64),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
Source unit M335.003 occupies lines 56–64: its docstring is at
lines 56–57, statement at lines 58–60 and proof at lines 60–64.
The section variables are at lines 37–38 and the original header at
lines 1–5. The full source file's SHA-256 is
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

- extracted only M335.003 and its docstring into the required focused
  `ValuationProof` module;
- changed the namespace from `LubinTate` to `Langlands.NYLL.LubinTate`;
- replaced the six source imports by the single published
  `StandardLocalField.Statements` import;
- expressed the theorem's type as the fully applied imported proposition
  and added its initial unfolding, retaining the remaining proof steps;
- retained `noncomputable section`, `open scoped ValuativeRel` and the
  exact section variables, and omitted the four namespace opens unused by
  this proof;
- replaced the module documentation, added the modification notice and
  wrote this paired Markdown.

The theorem name suffix and mathematical content are unchanged. All NYLL
names in the proof resolve to their published `Langlands.NYLL`
adaptations. The target module itself is unchanged.
