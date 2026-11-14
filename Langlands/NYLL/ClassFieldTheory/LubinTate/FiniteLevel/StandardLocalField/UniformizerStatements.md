# Target: the transported canonical uniformizer is a uniformizer (M335.021)

This module states, as a Prop-valued target without proof, exactly the
assertion of source unit M335.021, the theorem
`LubinTate.standardLocalFieldUniformizer_isUniformizer` at lines 300–312 of
Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/StandardLocalField.lean#L300-L312)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The theorem command
starts at line 302; lines 300–301 are its docstring, lines 302–304 its
statement and lines 304–312 its tactic proof. The source file's SHA-256 is
`88a5745b57cab3c3b2241d6ce5344b5f9e0ad214e200e77072e4ad6fdc1a217e`.
Its header, imports, section variables and opened namespaces (lines 1–38)
and the declarations through line 316 were read directly.

The original is available in the registered source
`external-lean-reuse-snapshots-2026-10-21`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`, with attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement`. No compatibility patch
(including the recorded patch10) changes this source module.

## Target

`Langlands.NYLL.LubinTate.standardLocalFieldUniformizer_isUniformizerStatement`
is a `def` returning `Prop`, with the source section parameters unchanged:

```
(K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
```

Its value is the exact source assertion

```
(standardLocalField K).valuation.IsUniformizer
  (standardLocalFieldUniformizer K : K)
```

Here `(standardLocalField K).valuation` is the valuation inherited by the
canonical local-field package `Langlands.NYLL.LubinTate.standardLocalField K`
from its complete discrete valuation `localCompleteDVF K`; it is
definitionally `ValuativeRel.valuation K`. The element is the underlying
field element of the M335.019 definition
`Langlands.NYLL.LubinTate.standardLocalFieldUniformizer K`, namely of the
chosen irreducible element `chosenIntegerRingUniformizer K` of `𝒪[K]`.
`IsUniformizer` is Mathlib's `Valuation.IsUniformizer`: for a valuation `v`
with `v.IsRankOneDiscrete`, `v.IsUniformizer π` means
`v π = ↑(Valuation.IsRankOneDiscrete.generator v)`, that is, the value of
`π` is the chosen generator of the value group that is `< 1`. The
`IsRankOneDiscrete` instance is the field `isRankOneDiscrete` of the
package's stored `IsCompleteDiscrete` instance; since `IsRankOneDiscrete`
is a proposition, the choice of instance does not affect the target. This
is not the distinct NYLL predicate `MultiplicativeIntegerValuation.IsUniformizer`
(M122.040).

The target asserts this property; it does not prove it. The exact proof is
a separate later unit.

## Exact source correspondence

| Source unit and declaration | Adapted declaration | Type |
| --- | --- | --- |
| M335.021, theorem `LubinTate.standardLocalFieldUniformizer_isUniformizer`, lines 300–312 | `Langlands.NYLL.LubinTate.standardLocalFieldUniformizer_isUniformizerStatement : Prop` (with the parameters above) | `(standardLocalField K).valuation.IsUniformizer (standardLocalFieldUniformizer K : K)`, unchanged. |

## Imports and scope

The sole import is the M335.019 module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField.Uniformizer`,
submitted for review as the sibling definition candidate
`9fb83894-4f08-46fa-99bf-fa036c60ed18`; this target is integrated only
together with or after it.
It transitively supplies `standardLocalField`, its valuation and
rank-one discrete instance, and Mathlib's
`Mathlib.RingTheory.Valuation.Discrete.Basic`, where
`Valuation.IsUniformizer` is defined. It replaces the six upstream imports,
including the principal-unit and Teichmüller modules, none of which the
assertion uses.

Only the assertion of M335.021 is stated. Its proof, the coercion equation
M335.020 and all other source declarations are outside this unit.

## Attribution and complete modification record

The original 2026 copyright, Apache-2.0 release line and author header are
retained verbatim. The existing unmodified
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused. Their SHA-256
values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The retained NOTICE has no source-specific entry for this source file.

Worker 412 made these modifications on 14 November 2026:

- turned the source theorem into a Prop-valued `def` whose body is the
  theorem's type, renamed with the suffix `Statement`, and omitted its
  proof (lines 304–312);
- prefixed the declaration namespace `LubinTate` with `Langlands.NYLL`;
- replaced the six upstream imports by the one M335.019 import above;
- dropped the source's opened namespaces, `open scoped ValuativeRel` and
  `noncomputable section`, none of which the assertion needs;
- adapted the docstring to describe a target, replaced the module
  documentation, added the prominent modification notice in the Lean
  header, and wrote this paired Markdown.

The section variables and the asserted proposition are otherwise unchanged.
