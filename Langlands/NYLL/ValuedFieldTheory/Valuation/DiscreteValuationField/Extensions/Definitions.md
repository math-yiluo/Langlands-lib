# NYLL M108.001, .003, .004, .054: degree, ramification index, residue degree, defectlessness

The paired Lean file adapts four definitions of Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Extensions.lean`.
The pinned source file has SHA-256
`e8999a99fc7ff6c38bd68742b9c7779decfbb2d042f60779bd2386d7950232b5`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source definition after `ValuationTheory.DiscreteValuationField.ValuedExtension.` | Docstring | Definition | Adapted name after `Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.` |
| --- | --- | --- | --- | --- |
| M108.001 | `degree` | 40 | 41–42 | `degree` |
| M108.003 | `ramificationIndex` | 51–52 | 53–56 | `ramificationIndex` |
| M108.004 | `residueDegree` | 58–59 | 60–62 | `residueDegree` |
| M108.054 | `IsDefectless` | 492 | 493–495 | `IsDefectless` |

The source context, copied verbatim, is `namespace ValuationTheory` (line 26),
`noncomputable section` (line 28), `universe u v w x` (line 30),
`namespace DiscreteValuationField` and `namespace ValuedExtension`
(lines 32–33), the four variable lines 35–38

```lean
variable {K : Type u} {L : Type w} [Field K] [Field L]
variable [Algebra K L] [FiniteDimensional K L]
variable (base : DVF.{u, v} K) (target : DVF.{w, x} L)
variable [base.valuation.HasExtension target.valuation]
```

and the closing lines 497–500. The text of the source module docstring
(lines 16–24) is kept under an extended title and after a modification
notice.

The other declarations of the source file are not part of this module:
M108.002 `degree_eq_finrank` (lines 44–49), M108.005–.051 (the integer,
residue and unit maps and their lemmas, lines 64–482), M108.052
`IsUnramified` (lines 484–486) and M108.053 `IsTotallyRamified`
(lines 488–490). None of the four definitions mentions them.

The definitions use the published
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF` (M103.002), its
abbreviations `DVF.valuation`, `DVF.valuationSubring` (M103.003) and
`DVF.maximalIdeal` (M103.007) from
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic`,
and the Mathlib names `Module.finrank`, `Valuation.HasExtension`,
`Ideal.ramificationIdx'` and `Ideal.inertiaDeg`. The algebra structure of the
target valuation subring over the base valuation subring, which
`Ideal.ramificationIdx'` and `Ideal.inertiaDeg` need, is Mathlib's instance
`Valuation.HasExtension.instAlgebra_valuationSubring`, found from the
`HasExtension` variable; a `#synth` check against the adapted module
returned exactly this instance.

## Definitions and complete telescopes

The definitions are copied verbatim. Lean includes in each definition only
the variables it uses, so the elaborated telescopes, which a check with
`#check` confirmed, are as follows (universe parameters `u v w x`).

- `degree`: `{K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]`
  and the explicit arguments `(_base : DVF.{u, v} K) (_target : DVF.{w, x} L)`,
  with value in `ℕ`. Neither `[FiniteDimensional K L]` nor the
  `HasExtension` instance is included, as in the source.
- `ramificationIndex` and `residueDegree`: `{K : Type u} {L : Type w}
  [Field K] [Field L] [Algebra K L] (base : DVF.{u, v} K)
  (target : DVF.{w, x} L) [base.valuation.HasExtension target.valuation]`,
  with value in `ℕ`. `[FiniteDimensional K L]` is not included.
- `IsDefectless`: the telescope of `ramificationIndex`, with value in
  `Prop`.

### M108.001

```lean
def degree (_base : DVF.{u, v} K) (_target : DVF.{w, x} L) : ℕ :=
  Module.finrank K L
```

The degree of the extension is `Module.finrank K L`. The two DVF arguments
only record which valued fields are meant.

### M108.003

```lean
noncomputable def ramificationIndex : ℕ :=
  Ideal.ramificationIdx'
    (base.maximalIdeal : Ideal base.valuationSubring)
    (target.maximalIdeal : Ideal target.valuationSubring)
```

The ramification index is Mathlib's `Ideal.ramificationIdx'` of the maximal
ideal of the target valuation subring over the maximal ideal of the base
valuation subring.

### M108.004

```lean
noncomputable def residueDegree : ℕ :=
  (target.maximalIdeal : Ideal target.valuationSubring).inertiaDeg
    base.valuationSubring
```

The residue degree is Mathlib's `Ideal.inertiaDeg` of the target maximal
ideal over the base valuation subring.

### M108.054

```lean
def IsDefectless : Prop :=
  degree base target =
    ramificationIndex base target * residueDegree base target
```

The extension is defectless when its degree equals the product of its
ramification index and residue degree.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the definitions lie in
   `Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension`.
2. Replace the source imports
   `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ResidueField` and
   `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete`
   (lines 7–8) by the published
   `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic`,
   which supplies `DVF` and its abbreviations. The six Mathlib imports of
   lines 9–14 are kept.
3. Extend the module docstring title to name the four definitions and add a
   modification notice before the source docstring text.
4. Omit the other declarations of the source file (listed above).
5. The four definitions, their docstrings, the variable lines and the
   namespace, section and universe context are otherwise unchanged. No
   helper declaration or instance is added.

These are definitions only. They discharge no host class-formation, cup,
transfer, Tate or reciprocity target.

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
