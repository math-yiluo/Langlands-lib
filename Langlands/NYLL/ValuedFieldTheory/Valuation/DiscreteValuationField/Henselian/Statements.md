# NYLL M104.001–.004, .013, .015: idempotent lifting and Henselian DVF targets

The paired Lean file adapts the statements of six theorems of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Henselian.lean`.
The pinned source file has SHA-256
`cce4a6ecfed6076732a5041ad23935a638de6eb5c3c35287d289c8b1717e0cf2`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ValuationTheory.DiscreteValuationField.` | Docstring | Telescope and statement | Proof | Adapted target after `Langlands.NYLL.ValuationTheory.DiscreteValuationField.` |
| --- | --- | --- | --- | --- | --- |
| M104.001 | `idempotentPolynomial_monic` | 25–26 | 27–29 | 29–32 | `idempotentPolynomial_monicStatement` |
| M104.002 | `idempotentPolynomial_eval_mem_of_quotient_idempotent` | 34 | 35–38 | 38–43 | `idempotentPolynomial_eval_mem_of_quotient_idempotentStatement` |
| M104.003 | `idempotentPolynomial_derivative_eval_isUnit_of_quotient_idempotent` | 45–46 | 47–52 | 52–83 | `idempotentPolynomial_derivative_eval_isUnit_of_quotient_idempotentStatement` |
| M104.004 | `exists_idempotent_lift_of_surjective_henselianRing_ker` | 85–89 | 90–95 | 95–136 | `exists_idempotent_lift_of_surjective_henselianRing_kerStatement` |
| M104.013 | `HenselianDVF.valuationSubring_isDiscreteValuationRing` | 250 | 251–252 | 252–253 | `HenselianDVF.valuationSubring_isDiscreteValuationRingStatement` |
| M104.015 | `HenselianDVF.maximalIdeal_ne_bot` | 261 | 262–263 | 263–264 | `HenselianDVF.maximalIdeal_ne_botStatement` |

The source imports `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic`
and `Mathlib.RingTheory.Henselian` (lines 7–8) and has the context
`namespace ValuationTheory` (line 17), `noncomputable section` (line 19),
`universe u v` (line 21) and `namespace DiscreteValuationField` (line 23).
M104.013 and M104.015 lie in `namespace HenselianDVF` (line 197) with the
variables `{K : Type u} [Field K]` (line 199).

The other declarations of the source file are not part of this module:

- M104.005 `exists_idempotent_lift_of_henselianRing_mk` (lines 138–176),
  M104.006 `exists_idempotent_lift_of_henselianRing` (lines 178–188),
  M104.012 `HenselianDVF.exists_polynomial_lift_residue` (lines 218–248),
  M104.014 `HenselianDVF.henselianRing` (lines 255–259) and M104.016
  `HenselianDVF.exists_lift_root_simple` (lines 266–272) are outside this
  contribution. None of the six statements mentions them.
- M104.007–.011 (the structure `HenselianDVF`, its instance attribute and
  the four abbreviations `valuationSubring`, `maximalIdeal`, `residueField`
  and `residueMap`, lines 190–216) are already published in
  `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian.Definitions`,
  which this module imports.

The statements of M104.001–.004 use only Mathlib names: `Polynomial`,
`Polynomial.X`, `Polynomial.Monic`, `Polynomial.eval`,
`Polynomial.derivative`, `Ideal`, `Ideal.Quotient.mk`, `IsIdempotentElem`,
`IsUnit`, `Function.Surjective`, `RingHom`, `RingHom.ker`, `HenselianRing`
and `Nontrivial`. The statements of M104.013 and M104.015 use Mathlib's
`IsDiscreteValuationRing` and `⊥` and the published
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.HenselianDVF`,
`HenselianDVF.valuationSubring` (M104.008) and `HenselianDVF.maximalIdeal`
(M104.009).

## Targets and complete telescopes

M104.001–.004 bind their own types `R` (and `S`) with `Type*`, as in the
source, so they are universe polymorphic. M104.013 and M104.015 have,
before the binder shown, the binders of the source variable line 199:
implicit `{K : Type u}` and the instance `[Field K]`; `F` lives in
`HenselianDVF.{u, v} K` exactly as in the source.

### M104.001

```lean
def idempotentPolynomial_monicStatement
    {R : Type*} [CommRing R] [Nontrivial R] : Prop :=
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial R).Monic
```

In every nontrivial commutative ring `R`, the polynomial `X ^ 2 - X` is
monic.

### M104.002

```lean
def idempotentPolynomial_eval_mem_of_quotient_idempotentStatement
    {R : Type*} [CommRing R] {I : Ideal R} (a0 : R)
    (ha0 : IsIdempotentElem (Ideal.Quotient.mk I a0)) : Prop :=
    (Polynomial.X ^ 2 - Polynomial.X : Polynomial R).eval a0 ∈ I
```

If the class of `a0` modulo an ideal `I` is idempotent, then
`a0 ^ 2 - a0` lies in `I`. The source hypothesis `ha0` is kept although the
proposition does not mention it.

### M104.003

```lean
def idempotentPolynomial_derivative_eval_isUnit_of_quotient_idempotentStatement
    {R : Type*} [CommRing R] {I : Ideal R} (a0 : R)
    (ha0 : IsIdempotentElem (Ideal.Quotient.mk I a0)) : Prop :=
    IsUnit
      (Ideal.Quotient.mk I
        ((Polynomial.X ^ 2 - Polynomial.X : Polynomial R).derivative.eval a0))
```

Under the same hypothesis, the class of the value of the derivative
`2X - 1` at `a0` is a unit in `R ⧸ I`. The hypothesis `ha0` is kept as in
M104.002.

### M104.004

```lean
def exists_idempotent_lift_of_surjective_henselianRing_kerStatement
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f)
    [HenselianRing R (RingHom.ker f)]
    (e : S) (he : IsIdempotentElem e) : Prop :=
    ∃ e' : R, IsIdempotentElem e' ∧ f e' = e
```

For a surjective ring map `f : R →+* S` whose kernel is a Henselian ideal of
`R`, every idempotent `e` of `S` is the image of an idempotent `e'` of `R`.
The hypotheses `hf` and `he` are kept although the proposition does not
mention them.

### M104.013

```lean
def valuationSubring_isDiscreteValuationRingStatement
    (F : HenselianDVF.{u, v} K) : Prop :=
    IsDiscreteValuationRing F.valuationSubring
```

The valuation subring of a Henselian discretely valued field is a discrete
valuation ring.

### M104.015

```lean
def maximalIdeal_ne_botStatement (F : HenselianDVF.{u, v} K) : Prop :=
    F.maximalIdeal ≠ ⊥
```

The maximal ideal of that valuation subring is not the zero ideal.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the targets lie in
   `Langlands.NYLL.ValuationTheory.DiscreteValuationField` and its
   subnamespace `HenselianDVF`.
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
4. Replace the two source imports by the single import
   `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian.Definitions`,
   which publishes `HenselianDVF` and its abbreviations and itself imports
   the published DVF module and `Mathlib.RingTheory.Henselian`.
5. Omit the other declarations of the source file (listed above). Retain
   the namespaces, the noncomputable section, `universe u v` and the
   variable line 199.
6. Precede M104.002, M104.003 and M104.004 by
   `set_option linter.unusedVariables false in`: their propositions do not
   mention the hypotheses `ha0` (M104.002 and M104.003) and `hf`, `he`
   (M104.004), which the linter reports as unused. A check without the
   options gave exactly these four warnings. Each option affects only the
   declaration it precedes.
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
