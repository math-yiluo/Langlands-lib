# NYLL M043.009–.012: norms of finite cyclic representations and iterates

The paired Lean file adapts the statements of four theorems of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean`.
The pinned source file has SHA-256
`5ac5450e039760193ab008f2bed81158a543d2d9982515cd2e376baeadfe1284`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ClassFormation.` | Docstring | Telescope and statement | Proof | Adapted target after `Langlands.NYLL.ClassFormation.` |
| --- | --- | --- | --- | --- | --- |
| M043.009 | `rep_norm_eq_generatorPowerSum` | 218–219 | 220–224 | 224–253 | `rep_norm_eq_generatorPowerSumStatement` |
| M043.010 | `rep_action_pow_eq_iterate` | 255–256 | 257–259 | 259–261 | `rep_action_pow_eq_iterateStatement` |
| M043.011 | `rep_norm_eq_generatorIterateSum` | 263–264 | 265–270 | 270–275 | `rep_norm_eq_generatorIterateSumStatement` |
| M043.012 | `rep_action_pow_fixed` | 277–278 | 279–281 | 281–283 | `rep_action_pow_fixedStatement` |

The source imports
`Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.CoreFrobeniusNorm`
and `Mathlib.Dynamics.BirkhoffSum.Basic` (lines 7–8) and has the context
`universe u v` (line 18), `namespace ClassFormation` (line 20),
`open KummerTheory` and `open CyclicCohomology` (lines 22–23),
`noncomputable section` (line 27), `open CategoryTheory` (line 29) and
`open scoped BigOperators` (line 30). The four theorems have no source
`variable` binders: each binds its own group `Q` or `R` of type
`IntegralRepGroupType`.

The other declarations of the source file are not part of this module:

- M043.003 `conjugateStableAction` (line 73), M043.006
  `conjugateStableAction_coe` (line 106) and M043.007
  `relativeNorm_conjugateStableAction` (line 117) are in the separate
  contribution under `UniversalNormDescent/ConjugateStableAction/`.
- The private theorems M043.001, M043.002, M043.004 and M043.005 (lines 35,
  62, 80 and 88) and M043.008 `universalNormDescent_cyclic_lift_and_correction`
  (line 157) are outside this contribution. None of the four statements
  mentions them.

The statements use Mathlib's `Rep`, its fields `V` and `ρ`, `Rep.norm` with
`.hom`, `Subgroup.zpowers`, `Fintype.card`, `Fin`, finite sums `∑`, group
powers `^` and function iteration `f^[n]`, and the published
`Langlands.NYLL.IntegralRepGroupType` (M002.001, the abbreviation
`Type 0`).

## Targets and complete telescopes

Each target binds exactly the binders shown; there are no section
variables.

### M043.009

```lean
def rep_norm_eq_generatorPowerSumStatement
    {Q : IntegralRepGroupType} [Group Q] [Fintype Q]
    (B : Rep ℤ Q) (g : Q) (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (n : ℕ) (hcard : Fintype.card Q = n) (x : B.V) : Prop :=
    B.norm.hom x = ∑ i : Fin n, B.ρ (g ^ i.1) x
```

For a finite group `Q` all of whose elements are integer powers of `g`, and
`n` its cardinality, the norm of an integral representation `B` of `Q`
sends `x` to the sum of `B.ρ (g ^ i) x` over `i < n`. The hypotheses `hg` and
`hcard` are kept although the proposition does not mention them.

### M043.010

```lean
def rep_action_pow_eq_iterateStatement {R : IntegralRepGroupType} [Group R]
    (B : Rep ℤ R) (g : R) (n : ℕ) (x : B.V) : Prop :=
    B.ρ (g ^ n) x = ((B.ρ g)^[n]) x
```

The action of `g ^ n` is the `n`-fold iterate of the action map of `g`.

### M043.011

```lean
def rep_norm_eq_generatorIterateSumStatement
    {Q : IntegralRepGroupType} [Group Q] [Fintype Q]
    (B : Rep ℤ Q) (g : Q) (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (n : ℕ) (hcard : Fintype.card Q = n)
    (f : B.V → B.V) (hf : ∀ z, B.ρ g z = f z) (x : B.V) : Prop :=
    B.norm.hom x = ∑ i : Fin n, (f^[i.1]) x
```

Under the hypotheses of M043.009, and for a function `f` that agrees
pointwise with the action of `g`, the norm sends `x` to the sum of the
iterates `f^[i] x` over `i < n`. The hypotheses `hg`, `hcard` and `hf` are
kept although the proposition does not mention them.

### M043.012

```lean
def rep_action_pow_fixedStatement {R : IntegralRepGroupType} [Group R]
    (B : Rep ℤ R) (g : R) (x : B.V) (hx : B.ρ g x = x) (n : ℕ) : Prop :=
    B.ρ (g ^ n) x = x
```

An element fixed by `g` is fixed by every natural power of `g`. The
hypothesis `hx` is kept although the proposition does not mention it.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the targets lie in
   `Langlands.NYLL.ClassFormation`.
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
4. Replace the two source imports by
   `Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse`, which
   publishes `IntegralRepGroupType`, and
   `Mathlib.RepresentationTheory.Rep.Basic`, which defines `Rep` and
   `Rep.norm`.
5. Omit the other declarations of the source file (listed above), the
   declaration `universe u v`, which none of the four statements uses, and
   the opens of `KummerTheory` and `CyclicCohomology`: no name of those
   namespaces occurs in the four statements. Retain the namespace, the noncomputable section and the
   opens of `CategoryTheory` and `BigOperators`.
6. Precede M043.009, M043.011 and M043.012 by
   `set_option linter.unusedVariables false in`: their propositions do not
   mention the hypotheses `hg`, `hcard` (M043.009 and M043.011), `hf`
   (M043.011) and `hx` (M043.012), which the linter reports as unused. A
   check without the options gave exactly these six warnings in this module.
   Each option affects only the declaration it precedes.
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
