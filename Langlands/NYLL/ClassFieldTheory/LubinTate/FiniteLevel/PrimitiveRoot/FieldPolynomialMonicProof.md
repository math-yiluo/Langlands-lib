# Monicity of the primitive Lubin–Tate polynomial over the base field (M341.005)

This module proves
`Langlands.NYLL.LubinTate.standardLubinTatePrimitivePolynomialOverField_monicStatement`
by the theorem
`Langlands.NYLL.LubinTate.standardLubinTatePrimitivePolynomialOverField_monic`.
Its declared type is the fully applied imported target
`standardLubinTatePrimitivePolynomialOverField_monicStatement F π n`.
It preserves independent universes `u v`, implicit `{K : Type u} [Field K]`,
and explicit arguments
`(F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K)`,
`(π : F.valuationSubring)` and `(n : ℕ)`.
There is no uniformizer hypothesis: the result holds for every element `π`
of the valuation ring and every natural level `n`.

## Implemented proof

The published field polynomial is defined as

```lean
(standardLubinTatePrimitivePolynomial F π n).map
  (algebraMap F.valuationSubring K)
```

The coefficient map is the canonical inclusion of the valuation subring
into its base field. The `change` step unfolds the imported target and this
polynomial definition to expose exactly the displayed mapped polynomial.
The published theorem
`Langlands.NYLL.LubinTate.standardLubinTatePrimitivePolynomial_monic F π n`
proves monicity of the valuation-ring primitive polynomial, through its
Prop-valued statement definition. `Polynomial.Monic.map` transports that
monicity along `algebraMap F.valuationSubring K`, closing the goal. No
additional helper or hypothesis is needed. In particular, the proof also
covers `π = 0` and `n = 0`.

The entry module imports the published `PrimitiveRoot.FieldPolynomialStatements`
module and the published `DivisionPolynomial.Primitive.MonicProof` module
under `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel`.
The latter transitively supplies Mathlib's `Polynomial.Monic.map`.
All imported Lean/Markdown pairs are preserved.

## Original source and adaptations

The proof follows M341.005 (docstring line 90, theorem lines 91–94) of
Naganori Yamaguchi's NYLL ClassFieldTheory,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveRoot.lean`,
at commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The original header, universes and variable context, field polynomial
definition, and theorem were read directly in lines 1–160.
The source file SHA-256 is
`b9d4862f4873c982618ff0f591c73b251f7a6f6f3d4fc6e93134b6d4ecb732b4`.
Registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`;
its `files/Nyll/ClassFieldTheory/ANTHROPIC_FLT_SOURCE.md` does not list this
source file among the included Anthropic-derived files. No matching
project errata entry was found.

Worker 808 made these adaptations on 16 November 2026:

- Extracted only M341.005 into this focused module.
- Prefixed the namespace with `Langlands.NYLL`, preserving the complete
  source telescope and using the fully applied published target as the
  theorem's declared type.
- Replaced the broad source imports with the published statement module
  and the published prerequisite monicity proof module.
- Used `change` to expose the coefficient map and supplied that map
  explicitly to `Polynomial.Monic.map`, where the source inferred it.
- Replaced the module documentation, added the modification notice and
  wrote this paired explanation.

The original copyright, Apache-2.0 release line and author header remain
verbatim. Existing [LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are retained without edits.
Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
