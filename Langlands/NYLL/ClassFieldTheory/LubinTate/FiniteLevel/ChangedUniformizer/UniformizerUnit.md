# The changed uniformizer as a base-field unit: M391.009

This module extracts exactly source M391.009,
`LubinTate.standardLubinTateChangedUniformizerUnit`, as
`Langlands.NYLL.LubinTate.standardLubinTateChangedUniformizerUnit`.
The original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ChangedUniformizer.lean`,
lines 121–127](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ChangedUniformizer.lean#L120-L127),
with its docstring at line 120 and ambient context at lines 43–49,
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The complete original source file has SHA-256
`684df6d32cebe6a70087c9d6e4c9d70ae6913407f3c6d1ee2d70a6c975b912f7`.
The source file was read directly from the registered pinned snapshot,
under `external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`. The project errata lookup
contained no matching entry.

## Complete signature and defining value

The independent universes `u v`, the source parameter order and binder
kinds are retained. The complete telescope and codomain are:

```lean
{K : Type u} [Field K]
{F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K}
{π : F.valuationSubring}
(hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
(a : F.valuationSubringˣ) : Kˣ
```

The body is exactly the qualified source body, with the term variable
`u` renamed to `a`:

```lean
Langlands.NYLL.LubinTate.standardLubinTateBaseUniformizerUnit
  (Langlands.NYLL.LubinTate.standardLubinTateChangedUniformizer_isUniformizer hπ a)
```

The published changed parameter is the product
`(a : F.valuationSubring) * π` in the actual valuation subring of `F`.
The published preservation theorem proves that its image in `K` is a
uniformizer for the chosen valuation `F.toCompleteDVF.valuation`.
The base-uniformizer-unit definition then constructs the corresponding
unit of `K` using `Units.mk0` and the uniformizer's nonzero proof.
Thus the stored field element is the image of that product, and its
inverse is the field inverse. The result is a unit of the base field;
the original and changed uniformizers have their usual valuation-ring
uniformizer meaning.

## Published dependencies and focused imports

The module imports:

- `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.NormSubgroup.BaseUniformizerUnit.Definitions`,
  supplying the actual `standardLubinTateBaseUniformizerUnit`;
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer.IsUniformizerProof`,
  supplying the actual proved
  `standardLubinTateChangedUniformizer_isUniformizer` and, through its
  statement import, the actual changed-parameter definition.

Both use
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField`,
the shared FM package with its chosen complete discrete valuation and
finite residue field. Its independent value-group universe `v` remains
present. The construction reuses this package, its valuation-subring
coercion and the canonical Mathlib unit group without adding instances
or replacement structures. No finite-level extension or norm-subgroup
construction is needed.

## Adjacent coercion correspondence: M391.010

The adjacent source
`LubinTate.standardLubinTateChangedUniformizerUnit_coe`,
lines 131–138, has its docstring at line 129 and `@[simp]` at line 130.
Its full qualified claim is:

```lean
∀ {K : Type u} [Field K]
  {F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u, v} K}
  {π : F.valuationSubring}
  (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
  (a : F.valuationSubringˣ),
  (Langlands.NYLL.LubinTate.standardLubinTateChangedUniformizerUnit hπ a : K) =
    (Langlands.NYLL.LubinTate.standardLubinTateChangedUniformizer F π a : K)
```

Unfolding the actual changed-uniformizer-unit and base-uniformizer-unit
definitions reduces the left coercion to the stored value of `Units.mk0`,
which is precisely the right side. The equality is therefore
definitionally reflexive. The focused private probe checks this full
telescope by introducing its binders and closing with `rfl`.
It also directly assigns the unapplied definition to its complete
signature and checks the entire defining function against the displayed
body by `rfl`. The probe stays private; this public module contains one
definition and does not declare M391.010 or its simp attribute.

The executor's focused definition check on 16 November 2026 succeeded
with zero errors and warnings, and inspection confirmed kind `definition`
with level parameters `["u", "v"]`. The complete private probe also compiled
successfully with zero errors and warnings. These checks are recorded as
`dda2570f-4a74-42a1-bea9-ca89bd517bcb` (definition and inspection) and
`c412455f-1c43-4420-8ac5-e26a338a0645` (complete signature, defining body
and M391.010 reflexivity).

## Attribution and complete adaptation record

The original 2026 copyright, Apache-2.0 release line, authorship header
and declaration docstring are retained. The existing
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are reused unchanged,
with SHA-256 values respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
The retained NOTICE has no entry naming this source file.

Worker 231 made these adaptations on 16 November 2026:

- extracted only M391.009 and its docstring into this focused module;
- prefixed the declaration namespace and opened local-field namespace
  with `Langlands.NYLL`;
- replaced the twelve upstream imports with the two published imports above;
- renamed the term variable `u` to `a`, retaining universes `u v`;
- omitted the redundant outer `noncomputable section` and its closing
  `end`, retaining the declaration's explicit `noncomputable` modifier;
- replaced the broad upstream module documentation, added the prominent
  modification notice and wrote this paired Markdown.

Worker 309 supplied the prerequisite routing and a private feasibility
recipe. The executor's focused checks use the approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096`, Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`, through the project Lean
service. Independent review and Library integration establish publication.
