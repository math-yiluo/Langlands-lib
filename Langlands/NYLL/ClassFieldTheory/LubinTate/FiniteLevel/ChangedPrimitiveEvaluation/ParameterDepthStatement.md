# Changed-uniformizer principal-unit depth target: M393.001

The declaration
`Langlands.NYLL.LubinTate.standardLubinTateChangedUniformizer_sub_mem_maximalIdeal_powStatement`
is a closed `Prop`-valued definition of the exact proposition of NYLL
M393.001. It supplies an unproved target for a separate proof task.

For independent universes `u v`, the proposition is

```lean
∀ {K : Type u} [Field K]
  {F : LocalField.{u, v} K} {π : F.valuationSubring}
  (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
  (a : F.valuationSubringˣ) (n : ℕ)
  (ha : a ∈ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)),
  standardLubinTateChangedUniformizer F π a - π ∈
    F.maximalIdeal ^ (n + 2)
```

The field, its field instance, the local-field package and `π` are
implicit; `hπ`, `a`, `n` and `ha` are explicit and retain that order.
The hypothesis `hπ` says that the image of `π` in `K` is a uniformizer
for the chosen valuation. The hypothesis `ha` says that the valuation-ring
unit `a` differs from one by an element of the `(n + 1)`-st power of the
maximal ideal. The conclusion places `aπ - π` in its `(n + 2)`-nd power.
The uniformizer hypothesis is retained even though this target definition
does not use its proof to construct the conclusion.

## Source and correspondence

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ChangedPrimitiveEvaluation.lean`,
lines 54–80](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ChangedPrimitiveEvaluation.lean#L54-L80).
The original declaration is
`LubinTate.standardLubinTateChangedUniformizer_sub_mem_maximalIdeal_pow`;
its ambient field, namespace and independent-universe context is at
lines 40–51. The complete source file was read directly and its SHA-256
verified as
`3af04c0de9d11f3e110fa1362c267072451627bfb90456f3b96174c2f22da9a4`.
It is readable in the registered pinned snapshot
`external-lean-reuse-snapshots-2026-10-21`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`, with attribution supplement
`nyll-classfieldtheory-fbd320cd-supplement`. The project errata lookup
contained no entry for this source.

Only the proposition of M393.001 is extracted. The source proof is not
included, and this module does not assert that the target holds.
The mapped-parameter and changed-polynomial evaluation results
M393.002–004 are outside this extraction.

## Actual published dependencies

The two focused imports are

- `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer.Definitions`;
- `Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration.Definitions`.

The first supplies
`Langlands.NYLL.LubinTate.standardLubinTateChangedUniformizer`,
whose body is `(a : F.valuationSubring) * π`, and imports the actual
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField`.
The local-field package retains its chosen complete discrete valuation
and finite residue field with independent field and value-group universes.
The second supplies the concrete subgroup
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup`,
whose carrier at depth `m` is
`{a | (a : F.valuationSubring) - 1 ∈ F.maximalIdeal ^ m}` for the actual
complete-DVF package. Both imports share the published complete-DVF
projections. No replacement interface, local-field package, subgroup,
instance or extra hypothesis is introduced.

## Adaptations and attribution

Worker 322 made the following changes on 16 November 2026:

1. Extracted only the proposition of M393.001 into the focused module
   `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.ChangedPrimitiveEvaluation.ParameterDepthStatement`.
   The original theorem and its proof are replaced by a closed `def`
   returning `Prop`, with `Statement` appended to the source name.
   The ambient `{K : Type u} [Field K]` and the theorem telescope are
   universally quantified in the definition body, preserving binder
   explicitness, order, types, hypotheses and conclusion.
2. Prefixed the declaration namespace and the opened local-field
   namespace with `Langlands.NYLL`.
3. Renamed the source term variable `u` to `a` and its membership
   hypothesis `hu` to `ha`, retaining both independent universe variables
   `u v` and the explicit annotation `LocalField.{u, v}`.
4. Replaced the eight upstream imports by the two focused published
   imports above. Removed the unused polynomial scope and the four
   unrelated valuation, valued-extension and ramification namespace
   opens. Retained `noncomputable section`.
5. Replaced the module documentation and adjusted the declaration
   docstring to describe an unproved target; added the modification
   notice in the source header and this paired Markdown.
6. Disabled the unused-variable linter only for this definition, so the
   named premises `hπ` and `ha` can remain exactly in the source telescope
   without warnings. This setting does not change the proposition.

The original 2026 copyright, Apache-2.0 release statement and authorship
header are retained. The existing `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` are unchanged.

## Verification environment

The statement is checked through the project Lean service in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0 with Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`. Declaration inspection checks
that the definition returns `Prop`; this is a statement artifact, with
the proof obligation retained for a separate task.
