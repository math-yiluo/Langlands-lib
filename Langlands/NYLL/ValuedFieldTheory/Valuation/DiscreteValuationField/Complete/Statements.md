# NYLL M107.002, .013, .014, .017, .022, .023, .032: complete DVF targets

The paired Lean file adapts the statements of seven theorems of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Complete.lean`.
The pinned source file has SHA-256
`509cbb37745761cf3689a905512378e430932d5e8e13988470cbf072d84e46b9`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ValuationTheory.DiscreteValuationField.` | Docstring | Telescope and statement | Proof | Adapted target after `Langlands.NYLL.ValuationTheory.DiscreteValuationField.` |
| --- | --- | --- | --- | --- | --- |
| M107.002 | `Valuation.isAdicComplete` | 38 | 39–40 | 41 | `Valuation.isAdicCompleteStatement` |
| M107.013 | `CompleteDVF.valuationSubring_isDiscreteValuationRing` | 149 | 150–151 | 152 | `CompleteDVF.valuationSubring_isDiscreteValuationRingStatement` |
| M107.014 | `CompleteDVF.isAdicComplete` | 154 | 155–156 | 156–160 | `CompleteDVF.isAdicCompleteStatement` |
| M107.017 | `CompleteDVF.mem_valuationSubring_iff` | 172 | 173–174 | 175 | `CompleteDVF.mem_valuationSubring_iffStatement` |
| M107.022 | `CompleteDVF.exists_uniformizer` | 200 | 201–202 | 203 | `CompleteDVF.exists_uniformizerStatement` |
| M107.023 | `CompleteDVF.uniformizer_mem_maximalIdeal` | 205 | 206–208 | 209 | `CompleteDVF.uniformizer_mem_maximalIdealStatement` |
| M107.032 | `CompleteDVF.maximalIdeal_ne_bot` | 307 | 308–309 | 309–318 | `CompleteDVF.maximalIdeal_ne_botStatement` |

The source imports the NYLL modules `Henselian`, `AdicPower` and
`ValuationTransport` of `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField`
(lines 7–9) and has the context `namespace ValuationTheory` (line 15),
`noncomputable section` (line 17), `universe u v w` (line 19) and
`namespace DiscreteValuationField` (line 21). M107.002 lies in
`namespace Valuation` (lines 23–97) with the variables
`{K : Type u} [Field K]` (line 25) and
`{Gamma : Type v} [LinearOrderedCommGroupWithZero Gamma]` (line 26). The
other six lie in `namespace CompleteDVF` (line 112) with the variables
`{K : Type u} [Field K]` (line 114).

The other declarations of the source file are not part of this module:

- M107.001 `Valuation.IsCompleteDiscrete` with its instance attribute
  (lines 28–36) and M107.006 `CompleteDVF` with its instance attributes
  (lines 99–110) are already published in
  `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Definitions`.
- M107.007–.012 (the abbreviations `toHenselianDVF`, `toDVF`,
  `valuationSubring`, `maximalIdeal`, `residueField` and `residueMap`,
  lines 116–147) are already published in
  `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Projections`,
  which this module imports (it imports `Complete.Definitions` and
  `Henselian.Definitions`).
- M107.021 `CompleteDVF.residue_surjective` (lines 195–198) is already
  published as the target `CompleteDVF.residue_surjectiveStatement` in
  `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.ResidueSurjectivityStatement`.
- M107.003 (the instance `isCompleteDiscrete_comap_ringEquiv`, lines
  43–73), M107.004, M107.005, M107.015, M107.016, M107.018–.020,
  M107.024–.031 and M107.033–.035 are outside this contribution. None of
  the seven statements mentions them.

The statements use Mathlib's `Valuation`, `Valuation.valuationSubring`,
`Valuation.IsUniformizer`, `IsLocalRing.maximalIdeal`, `IsAdicComplete`,
`IsDiscreteValuationRing`, `Exists`, `≤` (written `<=` as in the source)
and `⊥`, and the published NYLL declarations
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete`
(M107.001), `CompleteDVF` with its field `valuation` (M107.006),
`CompleteDVF.valuationSubring` (M107.009) and `CompleteDVF.maximalIdeal`
(M107.010). The instance arguments needed by `F.valuation.IsUniformizer`
are found, as in the source, through the published instance attributes on
`CompleteDVF.instValueGroup`, `CompleteDVF.instCompleteDiscrete` and
`Valuation.IsCompleteDiscrete.isRankOneDiscrete`.

## Targets and complete telescopes

M107.002 has, before the binders shown, the binders of the source variable
lines 25 and 26: implicit `{K : Type u}`, `[Field K]`, implicit
`{Gamma : Type v}` and `[LinearOrderedCommGroupWithZero Gamma]`. The other
targets have those of line 114: implicit `{K : Type u}` and `[Field K]`;
`F` lives in `CompleteDVF.{u, v} K` exactly as in the source.

### M107.002

```lean
def isAdicCompleteStatement (val : _root_.Valuation K Gamma) [IsCompleteDiscrete val] : Prop :=
    IsAdicComplete (IsLocalRing.maximalIdeal val.valuationSubring) val.valuationSubring
```

For a valuation `val` on `K` with a complete discrete valuation instance,
the valuation subring is complete for the adic topology of its maximal
ideal. The instance argument `[IsCompleteDiscrete val]` is kept as in the
source.

### M107.013

```lean
def valuationSubring_isDiscreteValuationRingStatement (F : CompleteDVF.{u, v} K) : Prop :=
    IsDiscreteValuationRing F.valuationSubring
```

The valuation subring of a complete discretely valued field is a discrete
valuation ring.

### M107.014

```lean
def isAdicCompleteStatement (F : CompleteDVF.{u, v} K) : Prop :=
    IsAdicComplete F.maximalIdeal F.valuationSubring
```

That valuation subring is complete for the adic topology of its maximal
ideal `F.maximalIdeal`.

### M107.017

```lean
def mem_valuationSubring_iffStatement (F : CompleteDVF.{u, v} K) (x : K) : Prop :=
    x ∈ F.valuation.valuationSubring ↔ F.valuation x <= 1
```

An element `x : K` lies in the valuation subring of the chosen valuation
if and only if its valuation is at most `1`.

### M107.022

```lean
def exists_uniformizerStatement (F : CompleteDVF.{u, v} K) : Prop :=
    Exists (fun pi : F.valuationSubring => F.valuation.IsUniformizer (pi : K))
```

Some element of the valuation subring is a uniformizer of the chosen
valuation.

### M107.023

```lean
def uniformizer_mem_maximalIdealStatement (F : CompleteDVF.{u, v} K)
    {pi : F.valuationSubring} (hpi : F.valuation.IsUniformizer (pi : K)) : Prop :=
    pi ∈ F.maximalIdeal
```

Every uniformizer `pi` of the valuation subring lies in the maximal ideal.
The source hypothesis `hpi` is kept although the proposition does not
mention it.

### M107.032

```lean
def maximalIdeal_ne_botStatement (F : CompleteDVF.{u, v} K) : Prop :=
    F.maximalIdeal ≠ ⊥
```

The maximal ideal of the valuation subring is not the zero ideal.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the targets lie in
   `Langlands.NYLL.ValuationTheory.DiscreteValuationField.Valuation` and
   `Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF`.
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
4. Replace the three source imports by the single import
   `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Projections`,
   which supplies every NYLL declaration the statements use.
5. Omit the other declarations of the source file (listed above) and the
   universe `w`, which only the omitted instance M107.003 uses (the
   declaration is `universe u v`). Retain the namespaces, the noncomputable
   section and the variable lines 25, 26 and 114.
6. Precede M107.023 by `set_option linter.unusedVariables false in`: its
   proposition does not mention the hypothesis `hpi`, which the linter
   reports as unused. A check without the option gave exactly this one
   warning. The option affects only that declaration.
7. No helper declaration or instance is added.

These are exact source statements as named propositions, without published
proofs. They discharge no host class-formation, cup, transfer, Tate or
reciprocity target.

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
