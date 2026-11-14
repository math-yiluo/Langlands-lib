# Changed-uniformizer preservation target: M391.003

This module defines the single closed proposition
`Langlands.NYLL.LubinTate.standardLubinTateChangedUniformizer_isUniformizerStatement`.
It states that multiplying a chosen integral uniformizer by a unit of the
same valuation ring gives another uniformizer for the chosen valuation.
It supplies an unproved target for separate proof work.

For independent universes `u v`, its complete proposition is:

```lean
∀ {K : Type u} [Field K] {F : LocalField.{u, v} K}
  {π : F.valuationSubring}
  (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
  (u : F.valuationSubringˣ),
  F.toCompleteDVF.valuation.IsUniformizer
    (standardLubinTateChangedUniformizer F π u : K)
```

Here `LocalField` is the actual published
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField`.
The changed parameter is the actual published
`Langlands.NYLL.LubinTate.standardLubinTateChangedUniformizer`.
The field, its field instance, local-field package and original integral
element remain implicit. The uniformizer proof `hπ` and unit `u` remain
explicit, in that order. The value-group universe is independent of the
field universe. There are no additional parameters or hypotheses.

## Original source and exact correspondence

The original is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ChangedUniformizer.lean`,
lines 69–76](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ChangedUniformizer.lean#L69-L76).
The complete source file has SHA-256
`684df6d32cebe6a70087c9d6e4c9d70ae6913407f3c6d1ee2d70a6c975b912f7`.
Its readable pinned snapshot is registered under
`external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`. The source header, imports,
universe and namespace context, definition, defining equality, preservation
theorem and following declarations through line 100 were read directly.
The project errata lookup contained no matching entry.

| Source unit | Source declaration | Adapted declaration |
| --- | --- | --- |
| M391.003, line 69 | `LubinTate.standardLubinTateChangedUniformizer_isUniformizer` | `Langlands.NYLL.LubinTate.standardLubinTateChangedUniformizer_isUniformizerStatement` |

The source theorem's entire telescope and conclusion are enclosed in
universal quantifiers inside a `def` returning `Prop`. The theorem proof
is omitted. This changes the theorem into its exact proposition target,
retaining the original binder names, order, explicitness, universes,
coercions and mathematical proposition after namespace qualification.

## Published dependency and source proof correspondence

The sole import is
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer.Definitions`.
It supplies source M391.001's actual changed-parameter definition and,
through the published shared LocalField module, the chosen local-field
package, valuation subring and uniformizer predicate. No replacement
local-field interface, instances or stronger hypotheses are introduced.

Source M391.002, `standardLubinTateChangedUniformizer_eq_unit_mul`
(lines 60–65), is the defining equality
`standardLubinTateChangedUniformizer F π u =
(u : F.valuationSubring) * π`. It follows by `rfl` against the published
M391.001 definition. It is not required as a separate imported declaration
or a new prerequisite unit for this target.

The source proof of M391.003 applies Mathlib's
`Valuation.IsUniformizer.of_associated` to `hπ`, with the association supplied
by `associated_unit_mul_right π (u : F.valuationSubring) u.isUnit`.
These existing Mathlib declarations express preservation under association
and association with a unit multiple, respectively. This explains the source
proof correspondence; this module contains no proof of the target.
Changed level fields, generators and norm subgroups are outside this unit.

## Adaptations and attribution

Worker 231 made these changes on 14 November 2026:

- extracted only M391.003's proposition into this focused `Statements` module;
- replaced its theorem with the closed Prop definition and `Statement` suffix;
- prefixed the declaration and opened namespaces with `Langlands.NYLL`;
- replaced the twelve upstream imports with the published definition import above;
- omitted the unused noncomputable section, replaced the module and declaration
  documentation, and added the modification notice and this paired Markdown;
- disabled the unused-variable linter only for this definition because the
  retained hypothesis name `hπ` does not occur in the conclusion.

No mathematical compatibility patch is needed. The original 2026 copyright,
Apache-2.0 release statement and authorship header remain intact. The existing
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained without changes.
Their SHA-256 values are, respectively,
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The retained NOTICE has no source-specific entry for this source file.

The target is checked through the project Lean service in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Compilation and declaration
inspection check that this is a proposition target; they do not prove it.
