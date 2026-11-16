# Equal-parameter polynomial map proof (M392.001)

This module proves the existing Library target
`Langlands.NYLL.LubinTate.standardLubinTatePolynomial_map_eq_of_parameter_eqStatement`.
The theorem is
`Langlands.NYLL.LubinTate.standardLubinTatePolynomial_map_eq_of_parameter_eq`
in module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.ParameterCongruence.PolynomialMapProof`.
Its declared type is exactly the closed target at independent universe levels
`u v w`; no parameters or hypotheses are added outside that proposition.

## Source correspondence

The original is Naganori Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ParameterCongruence.lean`,
M392.001, lines 43–50](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ParameterCongruence.lean#L43-L50)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The file SHA-256 is
`6df7cd16c757739d5f510d048535551845d4809251fb26c414186ecacb3a7f2f`.
The source header, imports, documentation, ambient context (including lines
33–39), selected theorem and following declarations through line 90 were
read directly.

The readable pinned snapshot is registered as
`external-lean-reuse-snapshots-2026-10-21` (content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`),
under `n-yamaguchi-0729--ClassFieldTheory/source/`. Its attribution supplement
is `nyll-classfieldtheory-fbd320cd-supplement` (content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No errata note for either source exists in the Library base used here.

The source's namespace `LubinTate` is prefixed with `Langlands.NYLL`.
The source theorem's ambient field context and explicit telescope have
already been closed into the imported target:

```lean
∀ {K : Type u} [Field K] (F : LocalField.{u, v} K)
  {R : Type w} [CommRing R]
  (f : F.valuationSubring →+* R)
  {π ϖ : F.valuationSubring} (h : f π = f ϖ),
  (standardLubinTatePolynomial F π).map f =
    (standardLubinTatePolynomial F ϖ).map f
```

Here `LocalField` is the published
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField`.
The polynomial is the published
`Langlands.NYLL.LubinTate.standardLubinTatePolynomial`, namely
`X ^ q + C π * X` with `q = Nat.card F.residueField`.
The ring `R` is arbitrary and commutative; the parameters belong to the
valuation ring, and their images under `f` agree. There is no uniformizer
premise. The field, value-group and target-ring universe levels remain
independent.

## Implemented Lean proof

The proof first introduces the exact closed telescope in its published
order. It then uses the original source proof unchanged:

```lean
simp [standardLubinTatePolynomial, h]
```

Unfolding the polynomial and simplifying its coefficient map turns the two
sides into `X ^ q + C (f π) * X` and `X ^ q + C (f ϖ) * X`.
The simplifier rewrites the first coefficient using `h : f π = f ϖ`,
closing the equality. This is the proof at source line 50, preceded only by
introductions required by the Library's closed target.

The sole import is the actual `PolynomialMapStatement` module. Its published
dependencies supply the shared local-field package, polynomial definition
and Mathlib polynomial-map API. This proof introduces no replacement
interface, instance or axiom and changes no published dependency. It proves
only M392.001.

## Adaptations and attribution

Worker 660 made these modifications on 16 November 2026:

- Extracted M392.001 into this focused proof module, omitted the other
  source declarations and prefixed the namespace with `Langlands.NYLL`.
- Replaced the source's full `DivisionPolynomial` import by the actual
  published target module and used that closed Prop as the theorem's type,
  with explicit universe levels `.{u, v, w}`.
- Introduced the target's quantified variables before the unchanged source
  simplification proof. Omitted the unused `noncomputable section`,
  `open scoped Polynomial` and namespace opening.
- Replaced the module documentation, adapted the theorem's descriptive
  docstring, and added the modification notice and this Markdown.

The original copyright, author and Apache-2.0 release header are retained
verbatim. The existing [LICENSE](../../../../../../licenses/NYLL/LICENSE)
and [NOTICE](../../../../../../licenses/NYLL/NOTICE) remain unchanged.
Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
