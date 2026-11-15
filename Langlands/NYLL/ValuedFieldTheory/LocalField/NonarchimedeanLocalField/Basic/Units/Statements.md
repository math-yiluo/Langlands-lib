# NYLL M128.007, .018: the valuation of a quotient and injectivity of integer units

The paired Lean file adapts the statements of two theorems of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/Basic.lean`.
The pinned source file has SHA-256
`c696d08952343a0f668340bac35e2485e74b52134b0e205a3a4dc0653f48d25e`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `LocalFieldTheory.IsNonarchimedeanLocalField.` | Docstring | Telescope and statement | Proof | Adapted target after `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.` |
| --- | --- | --- | --- | --- | --- |
| M128.007 | `v_div` | 105 | 106–109 | 109–110 | `v_divStatement` |
| M128.018 | `integerUnitsToFieldUnits_injective` | 194–195 | 196–198 | 198–202 | `integerUnitsToFieldUnits_injectiveStatement` |

The source imports `Mathlib.NumberTheory.LocalField.Basic` (line 7). The
context of the two theorems is `namespace LocalFieldTheory` (line 15),
`noncomputable section` (line 17), `universe u` (line 19),
`namespace IsNonarchimedeanLocalField` (line 21) and
`open scoped ValuativeRel WithZero` (line 23). There are no source
`variable` binders: each theorem binds its own field `K`.

The other declarations of the source file are not part of this module. The
statements use Mathlib's `Field`, `ValuativeRel`, `TopologicalSpace`,
`IsNonarchimedeanLocalField`, units `Kˣ` with division, `Additive.ofMul`,
integer subtraction and `Function.Injective`, and these published NYLL
declarations:

- `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v` (M128.001),
  the normalized integer valuation `Additive Kˣ → Int`, from
  `ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.Definitions`;
- `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits`
  (M128.016), the inclusion `𝒪[K]ˣ →* Kˣ` of valuation-integer units into
  field units, from
  `ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U016.Definitions`.

## Targets and complete telescopes

Each target binds exactly the binders shown; there are no section
variables.

### M128.007

```lean
def v_divStatement (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x y : Kˣ) : Prop :=
    v K (Additive.ofMul (x / y)) =
      v K (Additive.ofMul x) - v K (Additive.ofMul y)
```

For field units `x` and `y` of a nonarchimedean local field, the
normalized valuation of `x / y` is the valuation of `x` minus that of `y`.

### M128.018

```lean
def integerUnitsToFieldUnits_injectiveStatement
    (K : Type u) [Field K] [ValuativeRel K] : Prop :=
    Function.Injective (integerUnitsToFieldUnits K)
```

The inclusion of the units of the valuation integers into the field units
is injective. As in the source, this statement assumes only a field with a
valuative relation.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the targets lie in
   `Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField`.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The telescopes and the
   statements are copied verbatim, including the binder names, kinds and
   order; `: Prop :=` is appended to the last telescope line, and the line
   breaks are otherwise those of the source. The source proofs are omitted:
   this contribution publishes the proposition targets, and their proofs
   are separate work.
3. Prefix each source docstring with `Target:` and lower-case the first word
   after it; the wording is otherwise unchanged, and the lines are
   rewrapped. Replace the source module docstring by a description of this
   module with a modification notice that names the source theorems.
4. Replace the source import by the published modules
   `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.Definitions`
   (of `v`) and
   `Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.U016.Definitions`
   (of `integerUnitsToFieldUnits`), both of which import
   `Mathlib.NumberTheory.LocalField.Basic`.
5. Omit the other declarations of the source file. Retain the namespaces,
   the noncomputable section, the universe declaration and the scoped opens
   of `ValuativeRel` and `WithZero`.
6. No linter option is needed: every binder occurs in its proposition. No
   helper declaration or instance is added.

These are exact source statements as named propositions, without published
proofs. They discharge no host local-field, class-formation or reciprocity
target.

## Verification

The module passed a project Lean service check on 15 November 2026 with
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), with no errors or warnings.
Compilation is separate from independent semantic acceptance and
publication.

## Attribution

The Lean file retains the original copyright, Apache-2.0 release and author
header verbatim. The retained license is `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and the
notice is `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
