# Extensionality proof for Lubin–Tate series

This module proves NYLL source unit M336.002. The public theorem is
`Langlands.NYLL.LubinTate.LubinTateSeries.ext` in the entry module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Series.ExtProof`.
It proves the published target
`Langlands.NYLL.LubinTate.LubinTateSeries.extStatement` from
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Series.ExtStatement`
and carries the source `@[ext]` attribute.

## Statement proved

The theorem has independent universe parameters `u v`, in that order.
Its complete type, with binders in the target's order, is

```lean
∀ {K : Type u} [Field K]
  {F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K}
  {π : F.valuationSubring}
  {e e' : Langlands.NYLL.LubinTate.LubinTateSeries F π},
  e.toPowerSeries = e'.toPowerSeries → e = e'
```

Here the hypothesis is the explicit argument `h`. Thus two Lubin–Tate series
packages with the same field `K`, the same shared `LocalField` package `F` and
the same chosen element `π` are equal when their underlying power series over
`F.valuationSubring` are equal. As in the target, `π` is an arbitrary element
of the valuation subring and is not assumed to be a uniformizer. No other
hypothesis, instance or global declaration is added.

The target `extStatement h` is a proposition-valued definition whose body is
`e = e'`. The theorem states this body directly. Lean's `@[ext]` attribute
accepts only a theorem whose stated conclusion is an equality between two
variables. A development check placed the attribute on a theorem stated as
`extStatement h`, and Lean rejected it. The explicit equality is the target's
body after one definitional unfolding.

The anonymous `example` after the theorem assigns the unapplied constant `@ext`
to the complete telescope of the target, which ends in `extStatement h`.
It contains `K`, the `Field K` instance, `F`, `π`, `e`, `e'` and `h`, in that
order. This compile-time check confirms that the theorem's type exactly matches
the target's, binder by binder, up to the definitional unfolding of
`extStatement`.

## Implemented proof

The proof is the original four-step proof, unchanged. The structure
`LubinTateSeries F π` has one data field, `toPowerSeries`, and three
proof fields: `constantCoeff_eq_zero`, `coeff_one_eq_uniformizer` and
`map_residue_eq_frobenius`.

1. `cases e` and `cases e'` replace both packages by constructor
   applications with their four fields.
2. `cases h` substitutes the second power series by the first. This uses the
   hypothesis that the two `toPowerSeries` fields are equal.
3. The two constructor applications now have the same data field. Their three
   proof fields are proofs of the same propositions and are therefore
   definitionally equal by proof irrelevance, so `rfl` closes the goal.

The proof uses no imported lemma and introduces no auxiliary declaration.
The axiom report lists only Lean's standard `propext`, `Classical.choice` and
`Quot.sound`.

## Effect of the attribute

The `@[ext]` attribute registers `ext` for the `ext` tactic on
`LubinTateSeries F π`. As for any theorem with this attribute, Lean also
generates the companion theorem
`Langlands.NYLL.LubinTate.LubinTateSeries.ext_iff`, of type
`e = e' ↔ e.toPowerSeries = e'.toPowerSeries`, with the same implicit
parameters. This is Lean's standard effect of the retained attribute, not a
declaration written in this file. A private development
check confirmed that `ext1` proves `e = e'` from the power-series equality
by using this registration. The structure itself has no `@[ext]` attribute,
so no other extensionality theorem is registered for it.

## Original source

The original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FormalModule/Series.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/Series.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`. Its SHA-256 is
`78e883128e132584b700e3518c794774db5c458ea9a31a735519857b6204e3e9`, and it
is readable beneath
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered sources are `external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`.

| Source part | Lines | Adaptation |
| --- | --- | --- |
| Header | 1–5 | Retained verbatim, followed by a modification notice |
| `noncomputable section`, `universe u v` | 22, 24 | Retained |
| `namespace LubinTate`, `open LocalFieldTheory.DiscreteValuationField` | 26, 28 | Namespace prefixed with `Langlands.NYLL`; the `open` resolves within that prefix to the same shared `LocalField` namespace |
| `variable {K : Type u} [Field K]` | 30 | Retained |
| `namespace LubinTateSeries`, `variable {F : LocalField.{u, v} K} {π : F.valuationSubring}` | 56, 58 | Retained |
| Docstring and `@[ext]` | 60–62 | Retained verbatim |
| Theorem `ext`, its signature and proof | 63–68 | Retained verbatim |
| Closing `end` commands | 70–74 | Retained with the prefixed namespace name |

The structure at source lines 32–51 and its simp attributes at lines 53–55
are not repeated. They are the published M336.001 declaration in
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Series.Definitions`,
which this module imports through the target module.

## Dependencies and modification record

The sole direct import is the published target module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Series.ExtStatement`.
It imports the published definition module, so the theorem uses the
Library's `LubinTateSeries` structure and the shared `LocalField` package
unchanged. The target and definition Lean and Markdown files, and their
imports, are not modified.

The complete adaptations are the following:

- extraction of only the M336.002 theorem, with its docstring and attribute,
  into a focused proof file;
- the `Langlands.NYLL` namespace prefix;
- replacement of the original three imports by the single published target
  import; through the definition module it transitively supplies the two
  original Mathlib imports and the focused published `LocalField`
  definitions in place of the original NYLL module;
- the modified-file notice in the header, together with new module
  documentation;
- the anonymous complete-declaration check against `extStatement`.

The theorem name, binders, conclusion, attribute, docstring and proof are
unchanged. According to the NYLL port records, the original file has no
patch10 compatibility edits.

## Attribution

The original 2026 copyright, Apache-2.0 release line and author header for
Naganori Yamaguchi (assisted by OpenAI Codex) are preserved. The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are unchanged, with SHA-256
values `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Worker 462 made the listed modifications on 14 November 2026 and wrote this
Markdown. The project errata notes contain no entry for this source. The approved
environment is Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
