# Equal-parameter polynomial map target (M392.001)

This module extracts the theorem type of source unit M392.001,
`LubinTate.standardLubinTatePolynomial_map_eq_of_parameter_eq`, as an unproved
Prop-valued target. The original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ParameterCongruence.lean`,
lines 43–50](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ParameterCongruence.lean#L43-L50)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. Its file SHA-256 is
`6df7cd16c757739d5f510d048535551845d4809251fb26c414186ecacb3a7f2f`.
The header, imports, module documentation and context at lines 1–39,
the selected declaration at lines 41–51 and the following declarations
through line 90 were read directly.

The readable pinned snapshot is in registered source
`external-lean-reuse-snapshots-2026-10-21`, with content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`. The attribution supplement
is `nyll-classfieldtheory-fbd320cd-supplement`, with content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No errata note for either source exists in the Library base used here.

## Declaration and exact scope

`Langlands.NYLL.LubinTate.standardLubinTatePolynomial_map_eq_of_parameter_eqStatement`
is a closed `def` returning `Prop`, with independent universe parameters
`u v w`. Its body is exactly:

```lean
∀ {K : Type u} [Field K] (F : LocalField.{u, v} K)
  {R : Type w} [CommRing R]
  (f : F.valuationSubring →+* R)
  {π ϖ : F.valuationSubring} (h : f π = f ϖ),
  (standardLubinTatePolynomial F π).map f =
    (standardLubinTatePolynomial F ϖ).map f
```

Here `LocalField` denotes the published declaration
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField`.
The field `K` and its field instance are implicit, `F` is explicit,
the arbitrary target ring `R` and its commutative ring instance are implicit,
`f` is explicit, `π` and `ϖ` are implicit, and the image-equality premise `h`
is explicit. This preserves the source binder order and explicitness when
closing its ambient field context. The three universes remain independent.

The expression `standardLubinTatePolynomial` is the actual published
`Langlands.NYLL.LubinTate.standardLubinTatePolynomial` from M339.001:
the polynomial `X ^ q + C π * X` over `F.valuationSubring`, with
`q = Nat.card F.residueField`. The maps on polynomials are Mathlib's
`Polynomial.map`. Thus the target asserts equality after mapping coefficients
along any ring homomorphism whose values on the parameters agree.
There is no uniformizer hypothesis and no requirement that `R` be a field
or a nontrivial ring.

This file states only M392.001. It contains no proof of the target and
does not state any iterate, primitive-polynomial, evaluation or
ideal-congruence result from the remaining M392 units.

## Adaptations and dependencies

Worker 660 made these changes on 14 November 2026:

- Extracted the source theorem's type into a closed `def ... : Prop`,
  universally quantifying the ambient `{K : Type u} [Field K]` before
  the source's explicit theorem telescope. The source proof
  `simp [standardLubinTatePolynomial, h]` is omitted.
- Prefixed `LubinTate` with `Langlands.NYLL` and added the `Statement`
  suffix. The opened relative namespace resolves to the actual published
  `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`.
- Replaced the full upstream `DivisionPolynomial` import by
  `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Definitions`
  and `Mathlib.Algebra.Polynomial.Eval.Defs`. These provide the actual
  polynomial definition and polynomial coefficient map API.
- Omitted the unused `noncomputable section` and `open scoped Polynomial`,
  replaced the module documentation, adapted the declaration docstring
  to identify a target, and added the modification notice and this Markdown.
- Disabled the unused-variable linter only for this declaration, retaining
  the explicit source premise name `h` even though a proposition's
  conclusion does not refer to its proof.

No replacement local-field or polynomial interface, additional hypothesis,
instance or axiom is introduced. The proposition differs from the original
theorem type only by namespace qualification and closure of its ambient
context into the target.

## Attribution

The original copyright, Apache-2.0 release line and author header are
retained verbatim in the Lean file. The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused unchanged.
Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
