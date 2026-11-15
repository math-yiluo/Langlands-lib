# NYLL M105.002–.007, .011, .012: adic completeness under extension of scalars and positive powers

The paired Lean file adapts the statements of eight theorems of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/AdicPower.lean`.
The pinned source file has SHA-256
`df1f92c6b85a87ad4a27c319302f267a717b7f82c1cce10167c56b1c4793232d`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ValuationTheory.DiscreteValuationField.` | Docstring | Telescope and statement | Proof | Adapted target after `Langlands.NYLL.ValuationTheory.DiscreteValuationField.` |
| --- | --- | --- | --- | --- | --- |
| M105.002 | `mem_map_algebraMap_pow_iff_mem_pow_smul_top` | 54–55 | 56–60 | 60–62 | `mem_map_algebraMap_pow_iff_mem_pow_smul_topStatement` |
| M105.003 | `mem_map_algebraMap_pow_smul_top_iff` | 64 | 65–69 | 69–72 | `mem_map_algebraMap_pow_smul_top_iffStatement` |
| M105.004 | `smodEq_map_algebraMap_pow_smul_top_iff` | 74–75 | 76–80 | 80–82 | `smodEq_map_algebraMap_pow_smul_top_iffStatement` |
| M105.005 | `isPrecomplete_map_algebraMap_iff` | 84–85 | 86–88 | 88–110 | `isPrecomplete_map_algebraMap_iffStatement` |
| M105.006 | `isAdicComplete_map_algebraMap_iff` | 112–113 | 114–116 | 116–127 | `isAdicComplete_map_algebraMap_iffStatement` |
| M105.007 | `isAdicComplete_map_ringEquiv` | 129–130 | 131–134 | 134–148 | `isAdicComplete_map_ringEquivStatement` |
| M105.011 | `isHausdorff_of_isHausdorff_pow` | 204–205 | 206–209 | 209–213 | `isHausdorff_of_isHausdorff_powStatement` |
| M105.012 | `isPrecomplete_of_isPrecomplete_pow` | 215–216 | 217–220 | 220–243 | `isPrecomplete_of_isPrecomplete_powStatement` |

The source imports `Mathlib.RingTheory.AdicCompletion.Functoriality`
(line 7) and has the context `namespace ValuationTheory` (line 16),
`noncomputable section` (line 18), `namespace DiscreteValuationField`
(line 20) and the variables `{R : Type*} [CommRing R]` (line 22),
`{M : Type*} [AddCommGroup M] [Module R M]` (line 23) and
`{N : Type*} [AddCommGroup N] [Module R N]` (line 24).

The other declarations of the source file are not part of this module:

- M105.001 `isAdicComplete_of_linearEquiv` (lines 26–52) is already
  published, with its proof, as
  `Langlands.NYLL.ValuationTheory.DiscreteValuationField.isAdicComplete_of_linearEquiv`
  in `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianFinite.CompletenessProofs`.
  None of the eight statements mentions it; only the source proof of
  M105.007 uses it.
- M105.008–.010 (`isHausdorff_pow_of_isHausdorff`,
  `isPrecomplete_pow_of_isPrecomplete`,
  `isAdicComplete_pow_of_isAdicComplete`, lines 150–202) and M105.014
  (`isAdicComplete_of_le_of_pow_le`, lines 253–293) are outside this
  contribution.
- M105.013 (`isAdicComplete_of_isAdicComplete_pow`, lines 245–251) is
  already published with its proof, as
  `Langlands.NYLL.ValuationTheory.DiscreteValuationField.isAdicComplete_of_isAdicComplete_pow`
  in
  `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.AdicPowerCompletenessProof`.
  Its source proof uses M105.011 and M105.012, whose statements this module
  publishes.

All names in the statements are Mathlib's: `Ideal`, `Ideal.map`,
`algebraMap`, `Algebra`, `Submodule`, `⊤`, the scalar action `•` of an ideal
on a submodule, ideal powers `^`, `SModEq` with its notation
`x ≡ y [SMOD N]`, `IsHausdorff`, `IsPrecomplete`, `IsAdicComplete` and the
ring equivalence `R ≃+* S` with its coercion to `R →+* S`.

## Targets and complete telescopes

Every target has, before the binders shown, the binders of the source
variable line 22: implicit `{R : Type*}` and the instance `[CommRing R]`.
The targets M105.011 and M105.012 also have those of line 23, implicit
`{M : Type*}`, `[AddCommGroup M]` and `[Module R M]`; the other targets do
not mention `M`, so Lean does not include it, exactly as in the source.
No target mentions `N`.

### M105.002

```lean
def mem_map_algebraMap_pow_iff_mem_pow_smul_topStatement
    {S : Type*} [CommRing S] [Algebra R S] (I : Ideal R)
    (n : ℕ) {x : S} : Prop :=
    x ∈ (I.map (algebraMap R S)) ^ n ↔
      x ∈ I ^ n • (⊤ : Submodule R S)
```

For an `R`-algebra `S`, an ideal `I` of `R` and `n : ℕ`, an element of `S`
lies in the `n`-th power of the extended ideal `I S` if and only if it lies
in the `R`-submodule `I ^ n • S` of `S`.

### M105.003

```lean
def mem_map_algebraMap_pow_smul_top_iffStatement
    {S : Type*} [CommRing S] [Algebra R S] (I : Ideal R)
    (n : ℕ) {x : S} : Prop :=
    x ∈ ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S S) ↔
      x ∈ I ^ n • (⊤ : Submodule R S)
```

The same comparison with the left side written as the `S`-submodule
`(I S) ^ n • S` of `S`.

### M105.004

```lean
def smodEq_map_algebraMap_pow_smul_top_iffStatement
    {S : Type*} [CommRing S] [Algebra R S] (I : Ideal R)
    {x y : S} (n : ℕ) : Prop :=
    x ≡ y [SMOD ((I.map (algebraMap R S)) ^ n • ⊤ : Submodule S S)] ↔
      x ≡ y [SMOD (I ^ n • ⊤ : Submodule R S)]
```

Congruence modulo the `S`-submodule `(I S) ^ n • S` is the same as
congruence modulo the `R`-submodule `I ^ n • S`.

### M105.005

```lean
def isPrecomplete_map_algebraMap_iffStatement
    {S : Type*} [CommRing S] [Algebra R S] (I : Ideal R) : Prop :=
    IsPrecomplete (I.map (algebraMap R S)) S ↔ IsPrecomplete I S
```

`S` is precomplete for the extended ideal `I S`, as an `S`-module, if and
only if it is precomplete for `I`, as an `R`-module.

### M105.006

```lean
def isAdicComplete_map_algebraMap_iffStatement
    {S : Type*} [CommRing S] [Algebra R S] (I : Ideal R) : Prop :=
    IsAdicComplete (I.map (algebraMap R S)) S ↔ IsAdicComplete I S
```

The same equivalence for adic completeness (Hausdorff and precomplete).

### M105.007

```lean
def isAdicComplete_map_ringEquivStatement
    {S : Type*} [CommRing S] (I : Ideal R) (e : R ≃+* S)
    [IsAdicComplete I R] : Prop :=
    IsAdicComplete (I.map (e : R →+* S)) S
```

If `R` is `I`-adically complete and `e : R ≃+* S` is a ring equivalence,
then `S` is adically complete for the image ideal `I.map e`.

### M105.011

```lean
def isHausdorff_of_isHausdorff_powStatement
    (I : Ideal R) {n : ℕ} (_hn : 0 < n)
    [IsHausdorff (I ^ n) M] : Prop :=
    IsHausdorff I M
```

If `M` is Hausdorff for `I ^ n` with `0 < n`, then it is Hausdorff for `I`.
The source names the hypothesis `_hn`, so no linter option is needed.

### M105.012

```lean
def isPrecomplete_of_isPrecomplete_powStatement
    (I : Ideal R) {n : ℕ} (hn : 0 < n)
    [IsPrecomplete (I ^ n) M] : Prop :=
    IsPrecomplete I M
```

If `M` is precomplete for `I ^ n` with `0 < n`, then it is precomplete for
`I`. The source hypothesis `hn : 0 < n` is kept although the proposition
does not mention it, so that the target has every source hypothesis in the
source binder order.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the targets lie in
   `Langlands.NYLL.ValuationTheory.DiscreteValuationField`.
2. Replace each `theorem name … : statement := proof` by
   `def nameStatement … : Prop := statement`. The telescopes and the
   statements are copied verbatim, including the binder names, kinds and
   order and the line breaks. The source proofs are omitted: this
   contribution publishes the proposition targets, and their proofs are
   separate work.
3. Prefix each source docstring with `Target:` and lower-case the first word
   after it; the wording is otherwise unchanged, and the lines are
   rewrapped. Replace the source module docstring by a description of this
   module with a modification notice that names the source theorems.
4. Keep the source import `Mathlib.RingTheory.AdicCompletion.Functoriality`
   unchanged; no NYLL module is imported.
5. Omit the other declarations of the source file (listed above) and the
   variable line 24 for `N`, which none of the eight statements uses.
   Retain the namespaces, the noncomputable section and the variable lines
   22 and 23.
6. Precede M105.012 by `set_option linter.unusedVariables false in`: its
   proposition does not mention the hypothesis `hn`, which the linter
   reports as unused (a check without the option gave exactly this one
   warning). The option affects only that declaration.
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
