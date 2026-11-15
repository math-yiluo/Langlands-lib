# NYLL M109.007: valuation equivalence from equal valuation subrings

The paired Lean file adapts the statement of one theorem of Naganori
Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ValuationExtension.lean`.
The pinned source file has SHA-256
`63e3badbcec9715329fdf2a16627e8a0e7b7cbdfc9002ea69b5ada13be28e7bd`.
It is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`,
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Source correspondence

| Unit | Source theorem after `ValuationTheory.DiscreteValuationField.ValuedExtension.` | Docstring | Telescope and statement | Proof | Adapted target after `Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension.` |
| --- | --- | --- | --- | --- | --- |
| M109.007 | `valuation_isEquiv_of_valuationSubring_eq` | 209 | 210–214 | 215 | `valuation_isEquiv_of_valuationSubring_eqStatement` |

The source imports `Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Extensions`
(line 7) and has the context `namespace ValuationTheory` (line 18),
`noncomputable section` (line 20), `universe u v w x y` (line 22),
`namespace DiscreteValuationField` (line 24), `namespace ValuedExtension`
(line 25) and the variables
`{K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]` (line 27).
M109.007 lies in `section Comparison` (lines 205–266) with the variable
`(target : CompleteDVF.{w, x} L)` (line 207).

The other declarations of the source file, M109.001–.006 and
M109.008–.012 (lines 29–203 and 217–264), are not part of this module and
are not published; the statement of M109.007 does not mention them.

The statement uses Mathlib's `Valuation`, `Valuation.valuationSubring`,
`Valuation.IsEquiv` and `LinearOrderedCommGroupWithZero`, and the published
NYLL structure
`Langlands.NYLL.ValuationTheory.DiscreteValuationField.CompleteDVF`
(M107.006) with its field `valuation`, from
`Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Definitions`.
Here `target.valuation.valuationSubring` is Mathlib's
`Valuation.valuationSubring` of the valuation `target.valuation`, exactly
as in the source; the value-group instance it needs comes from the
published instance attribute on `CompleteDVF.instValueGroup`.

## Target and complete telescope

The target has, before the binders shown, the binders that the source
variable lines 27 and 207 contribute to it: implicit `{L : Type w}`,
`[Field L]` and explicit `(target : CompleteDVF.{w, x} L)`. As in the
source, the variables `{K : Type u}`, `[Field K]` and `[Algebra K L]` of
line 27 are not part of the telescope, because the statement does not
mention `K`; the port omits them from its variable line, which leaves the
elaborated telescope unchanged.

```lean
set_option linter.unusedVariables false in
/-- Target: equality of valuation subrings implies valuation equivalence. -/
def valuation_isEquiv_of_valuationSubring_eqStatement
    {Gamma' : Type y} [LinearOrderedCommGroupWithZero Gamma']
    (v' : _root_.Valuation L Gamma')
    (hsub : target.valuation.valuationSubring = v'.valuationSubring) : Prop :=
    target.valuation.IsEquiv v'
```

For a complete discretely valued field `L` with chosen valuation
`target.valuation` and any valuation `v'` on `L` with values in a linearly
ordered commutative group with zero `Gamma'`, if the two valuation
subrings are equal then the two valuations are equivalent. The hypothesis
`hsub` is kept although the proposition does not mention it; the source
proof applies the reverse direction of Mathlib's
`Valuation.isEquiv_iff_valuationSubring` to it.

## Modifications

Worker 5264 made these changes:

1. Prefix the namespace with `Langlands.NYLL`, so the target lies in
   `Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension`.
2. Replace `theorem valuation_isEquiv_of_valuationSubring_eq … : statement :=
   proof` by `def valuation_isEquiv_of_valuationSubring_eqStatement … : Prop :=
   statement`. The telescope and the statement are copied verbatim,
   including the binder names, kinds and order; `: Prop :=` is appended to
   the last telescope line, and the line breaks are otherwise those of the
   source. The source proof is omitted: this contribution publishes the
   proposition target, and its proof is separate work.
3. Prefix the source docstring with `Target:` and lower-case the first word
   after it; the wording is otherwise unchanged. Replace the source module
   docstring by a description of this module with a modification notice
   that names the source theorem, keeping its first sentence.
4. Replace the source import by the single import
   `Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Definitions`,
   which supplies every NYLL declaration the statement uses.
5. Omit the other declarations of the source file (listed above), the
   universes `u v`, which only the omitted variables and declarations use
   (the declaration is `universe w x y`), and the variables
   `{K : Type u}`, `[Field K]` and `[Algebra K L]` of line 27 (the variable
   line is `variable {L : Type w} [Field L]`). Retain the namespaces, the
   noncomputable section, `section Comparison` and its variable line 207.
6. Precede the target by `set_option linter.unusedVariables false in`: its
   proposition does not mention the hypothesis `hsub`, which the linter
   reports as unused. A check without the option gave exactly this one
   warning. The option affects only that declaration.
7. No helper declaration or instance is added.

This is an exact source statement as a named proposition, without a
published proof. It discharges no host class-formation, cup, transfer, Tate
or reciprocity target.

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
