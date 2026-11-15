# NYLL M350.003: the recursive correction coefficient

This module adapts exactly the definition `correctionCoefficient` of the
source module `Nyll.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient`.
The other declarations of that source module are not part of this unit.

## Original source

Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveCoefficient.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveCoefficient.lean`.
The source-file SHA-256 is
`bf28f5dfaf69641f687799e72c26590978e6bc0175b24d57a37324fcbf027588`.
The readable original is at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveCoefficient.lean`.
The registered sources are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and the
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable NYLL entry was found in `notes/errata/`.

## Source correspondence

| Source unit | Original declaration and lines | Adapted declaration (Lean lines) |
| --- | --- | --- |
| M350.003 | `LubinTate.SameUniformizer.correctionCoefficient`, 59–75 | `Langlands.NYLL.LubinTate.SameUniformizer.correctionCoefficient`, lines 40–56 |

The section context of source lines 21–32 is retained: a `noncomputable
section`, universes `u v w`, `open LocalFieldTheory.DiscreteValuationField`,
and the section variables

```lean
variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]
```

Inside `namespace Langlands.NYLL.LubinTate.SameUniformizer` the opened
namespace resolves to `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`,
so `LocalField`, `LubinTateSeries`, `HasLinearTerm` are the shared published
declarations (M334, M336, M347), and `K`, `F`, `π` and `σ` are implicit with
independent universes `u`, `v`, `w`. The explicit binders are, in source
order, `(hπ) (e ebar) {H} {L} (hH) (d) (hd : 2 ≤ d.degree)`; the proof `hH`
and the degree hypothesis `hd` are retained as parameters.

## Mathematical meaning

Write `O = F.valuationSubring` and `m = d.degree`, the total degree of the
exponent `d : σ →₀ ℕ` (Mathlib's `Finsupp.degree`). The published exact
M337.006 theorem

```lean
existsUnique_one_sub_uniformizer_pow_mul_eq hπ (hr : r ≠ 0) b :
  existsUnique_one_sub_uniformizer_pow_mul_eqStatement hπ hr b
```

asserts that for a uniformizer `π`, a natural number `r ≠ 0` and any
`b : O`, there is a unique `x : O` with `(1 - π ^ r) * x = b`. The
definition applies it with `r = m - 1`, whose nonvanishing follows from
`hd : 2 ≤ m` by `omega`, and with
`b = -normalizedDefectCoefficient hπ e ebar hH d` (the M350.001
coefficient):

```lean
correctionCoefficient hπ e ebar hH d hd : O :=
  Classical.choose
    (existsUnique_one_sub_uniformizer_pow_mul_eq hπ
      (by omega : d.degree - 1 ≠ 0)
      (-normalizedDefectCoefficient hπ e ebar hH d))
```

So `correctionCoefficient hπ e ebar hH d hd` is the witness chosen from this
unique-existence proof; it is the coefficient `c` with
`(1 - π ^ (m - 1)) * c = -normalizedDefectCoefficient hπ e ebar hH d`. That
defining equation is the separate source theorem M350.004 (target
`correctionCoefficient_specStatement`). In the source construction it is the
coefficient of the monomial `X^d` added to `H` to cancel the degree-`m`
defect coefficient (M352). The definition is noncomputable, as in the source.

## Dependencies and modification record

The direct imports are

- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient.NormalizedDefect`,
  the module of M350.001 `normalizedDefectCoefficient` (submitted together
  with this module, with its own Markdown, as one definition contribution),
  which also provides `LocalField`, `LubinTateSeries`, `HasLinearTerm` and
  `Finsupp.degree`;
- `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation.U006.Proofs`,
  the published module of the exact M337.006 proof
  `existsUnique_one_sub_uniformizer_pow_mul_eq` (accepted proof artifact
  `4f89fb16-074a-4542-bd3c-952f4b8f67a8` of proof Task 6719
  `c4a2ecfc-fc56-42bd-a51d-beccd4035d57`, against the target
  `existsUnique_one_sub_uniformizer_pow_mul_eqStatement`, statement artifact
  `b3ec010d-0b4c-4c00-af9e-551cac0756e2` of Task 6067).

The source obtains both through its single import of the whole source module
`Nyll.ClassFieldTheory.LubinTate.FormalModule.Reduction` (which imports
`CoefficientEquation`) and the preceding declaration in the same file. The
definition body consumes the exact published proofs, not unproved targets.

The complete adaptations are:

1. extraction of M350.003 into this definition-only file, omitting the
   source declarations M350.001 (imported), M350.002 and M350.004 (published
   separately as Prop targets and later proofs) and M350.005
   `correctionCoefficient_unique`, which is not requested;
2. the `Langlands.NYLL` prefix on the namespaces `LubinTate` and
   `SameUniformizer`;
3. the import replacements described above;
4. a modified-file notice in the header and a replaced module docstring.

The noncomputable section, universes, `open`, section variables, the
declaration docstring, name, binders, type and body (including the inline
`omega` side proof) are otherwise unchanged. This source module has no
patch10 edits. No coercion, simp attribute or global instance is introduced.

The original 2026 copyright, Apache-2.0 release line and author header are
preserved. Existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are
unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`; the
NOTICE has no entry specific to this source file, and the supplement's
`files/Nyll/ClassFieldTheory/ANTHROPIC_FLT_SOURCE.md` list of
Anthropic-derived files does not include it.
