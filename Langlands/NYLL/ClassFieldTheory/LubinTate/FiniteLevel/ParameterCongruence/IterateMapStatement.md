# Equal-parameter polynomial iterate map target (M392.002)

This module extracts the type of source unit M392.002,
`LubinTate.standardLubinTatePolynomialIterate_map_eq_of_parameter_eq`,
as an unproved Prop-valued target. The original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ParameterCongruence.lean`,
lines 54–69](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ParameterCongruence.lean#L54-L69)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The file SHA-256 is
`6df7cd16c757739d5f510d048535551845d4809251fb26c414186ecacb3a7f2f`.
Worker 343 read the complete source file, including the ambient independent
universes and field context at lines 33–39.

The readable pinned snapshot belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No matching source errata note exists in the Library base used here.

## Declaration and scope

`Langlands.NYLL.LubinTate.standardLubinTatePolynomialIterate_map_eq_of_parameter_eqStatement`
is a closed `def` returning `Prop`, with independent universes `u v w`.
Its body is exactly:

```lean
∀ {K : Type u} [Field K] (F : LocalField.{u, v} K)
  {R : Type w} [CommRing R]
  (f : F.valuationSubring →+* R)
  {π ϖ : F.valuationSubring} (h : f π = f ϖ) (n : ℕ),
  (standardLubinTatePolynomialIterate F π n).map f =
    (standardLubinTatePolynomialIterate F ϖ n).map f
```

Here `LocalField` is the published
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField`.
The field type `K` and its field instance are implicit, `F` is explicit,
the arbitrary target ring `R` and its commutative ring instance are implicit,
`f` is explicit, the two valuation-subring parameters are implicit, and
`h` and `n` are explicit, in that order. This retains the source telescope
and binder explicitness while closing the ambient field context.

The polynomial iterate is the published
`Langlands.NYLL.LubinTate.standardLubinTatePolynomialIterate` from M339.008.
It applies `(standardLubinTatePolynomial F π).comp` a total of `n` times
to `Polynomial.X`, where the standard polynomial is
`X ^ Nat.card F.residueField + C π * X`.
Thus this target says that equal images of the two parameters under `f`
give equal coefficient images of every such compositional iterate.
The coefficient map is Mathlib's `Polynomial.map`.
There is no uniformizer premise on either parameter, no field or
nontriviality premise on `R`, and no restriction on `n`.

This file contains only the M392.002 target. Its truth is not proved here;
the source induction proof is omitted. The other M392 targets and proofs
remain separate.

## Adaptations and dependencies

Worker 343 made these changes on 16 November 2026:

- Extracted only the theorem type into `def ... : Prop`, closing the
  source's ambient `{K : Type u} [Field K]` before its explicit telescope.
  All hypotheses and the polynomial equality are preserved.
- Prefixed the source namespace `LubinTate` with `Langlands.NYLL` and added
  the `Statement` suffix. The relative opened namespace resolves to the
  actual published `Langlands.NYLL.LocalFieldTheory.DiscreteValuationField`.
- Replaced the source's full `DivisionPolynomial` import with the single
  import
  `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Iterate.Definitions`.
  This supplies the actual LocalField and iterate definitions, together
  with the polynomial map API through its published imports. No theorem
  premise or replacement interface is introduced.
- Omitted the source proof, unused `noncomputable section` and unused
  `open scoped Polynomial`; replaced the module documentation, adapted the
  docstring to identify a target, and added the modification notice and
  this Markdown.
- Disabled the unused-variable linter only for this declaration to retain
  the explicit source premise name `h` even though the conclusion does
  not depend on its proof.

There are no additional hypotheses, instances or axioms.

## Attribution

The Lean header preserves the original copyright, Apache-2.0 release line
and author credit. The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are retained unchanged.
Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
