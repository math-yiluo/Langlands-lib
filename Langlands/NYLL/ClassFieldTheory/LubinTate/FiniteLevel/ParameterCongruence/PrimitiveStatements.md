# Parameter congruence targets for primitive Lubin–Tate polynomials (M392.003–005)

This module extracts exactly the theorem types of M392.003–005 from Naganori
Yamaguchi's
[`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ParameterCongruence.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ParameterCongruence.lean#L72-L144)
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, as closed, unproved
`def` declarations returning `Prop`. The original file's SHA-256 is
`6df7cd16c757739d5f510d048535551845d4809251fb26c414186ecacb3a7f2f`.
Its complete contents were read directly, including the header, imports,
independent universes and ambient field context at lines 33–39, and all three
selected statements and proofs.

The readable pinned snapshot is registered as
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The Library errata lookup contained no note for either source.

## Shared objects and quantifiers

All three full declaration names are in `Langlands.NYLL.LubinTate`.
They use independent universes `u v w`. Each body begins with implicit
`{K : Type u} [Field K]`, explicit
`(F : LocalField.{u, v} K)`, implicit `{R : Type w} [CommRing R]`,
and explicit `(f : F.valuationSubring →+* R)`.
The parameters `{π ϖ : F.valuationSubring}` are implicit, the hypothesis `h`
is explicit, and `(n : ℕ)` is explicit. The evaluation targets also have
explicit `(x : R)` after `n`; the ideal target has explicit `(I : Ideal R)`
immediately after `f`.

Here `LocalField` is the actual published
`Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField`,
and the primitive polynomial is the actual published
`Langlands.NYLL.LubinTate.standardLubinTatePrimitivePolynomial`.
Its value at `F`, `π`, and `n` is
`(standardLubinTatePolynomialIterate F π n) ^ (Nat.card F.residueField - 1)
  + Polynomial.C π`
in `Polynomial F.valuationSubring`. No replacement objects are introduced.

The target ring is any commutative ring, including the trivial ring.
Neither parameter has a uniformizer premise. In the third target the ideal
is arbitrary; it need not be prime, maximal or proper.

## Exact source correspondence

The names in the table are relative to `Langlands.NYLL.LubinTate`.
Each source name is the target name without its `Statement` suffix,
in the original `LubinTate` namespace.

| Source unit and lines | Target declaration | Meaning |
| --- | --- | --- |
| M392.003, 72–81 | `standardLubinTatePrimitivePolynomial_map_eq_of_parameter_eqStatement` | Equal parameter images imply equality of the coefficient-mapped primitive polynomials at every `n`. |
| M392.004, 85–99 | `standardLubinTatePrimitivePolynomial_eval₂_eq_of_parameter_eqStatement` | Equal parameter images imply equal primitive-polynomial evaluations at every `n` and `x`. |
| M392.005, 104–144 | `standardLubinTatePrimitivePolynomial_eval₂_sub_mem_of_parameter_sub_memStatement` | Parameter-image difference in `I` implies that the difference of the two evaluations at the same `n` and `x` belongs to `I`. |

The first proposition is exactly:

```lean
∀ {K : Type u} [Field K] (F : LocalField.{u, v} K)
  {R : Type w} [CommRing R]
  (f : F.valuationSubring →+* R)
  {π ϖ : F.valuationSubring} (h : f π = f ϖ) (n : ℕ),
  (standardLubinTatePrimitivePolynomial F π n).map f =
    (standardLubinTatePrimitivePolynomial F ϖ n).map f
```

The second proposition is exactly:

```lean
∀ {K : Type u} [Field K] (F : LocalField.{u, v} K)
  {R : Type w} [CommRing R]
  (f : F.valuationSubring →+* R)
  {π ϖ : F.valuationSubring} (h : f π = f ϖ)
  (n : ℕ) (x : R),
  Polynomial.eval₂ f x
      (standardLubinTatePrimitivePolynomial F π n) =
    Polynomial.eval₂ f x
      (standardLubinTatePrimitivePolynomial F ϖ n)
```

The third proposition is exactly:

```lean
∀ {K : Type u} [Field K] (F : LocalField.{u, v} K)
  {R : Type w} [CommRing R]
  (f : F.valuationSubring →+* R) (I : Ideal R)
  {π ϖ : F.valuationSubring} (h : f π - f ϖ ∈ I)
  (n : ℕ) (x : R),
  Polynomial.eval₂ f x
        (standardLubinTatePrimitivePolynomial F π n) -
      Polynomial.eval₂ f x
        (standardLubinTatePrimitivePolynomial F ϖ n) ∈ I
```

Coefficient maps and evaluations are Mathlib's `Polynomial.map` and
`Polynomial.eval₂`. The latter applies `f` to each coefficient and evaluates
the resulting polynomial at `x`. The subtraction order in both the ideal
premise and conclusion is `π` followed by `ϖ`, exactly as in the source.

These are definitions of the three propositions, not proofs of them.
The source proofs of coefficient-map equality, evaluation equality and
ideal congruence are omitted. M392.001–002 and all proof declarations are
outside this module.

## Adaptations and imports

Worker 323 made these modifications on 16 November 2026:

- Extracted the three theorem types into closed `def ... : Prop`
  declarations, placing the source's ambient `{K : Type u} [Field K]`
  first under each universal quantifier. Every other binder, its
  explicitness, its order, and the independent universes are retained.
- Prefixed `LubinTate` with `Langlands.NYLL` and added `Statement` suffixes.
  The relative `open LocalFieldTheory.DiscreteValuationField` resolves to
  the published `Langlands.NYLL` namespace.
- Replaced the upstream full `DivisionPolynomial` import by the published
  `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Primitive.Definitions`
  and `Mathlib.Algebra.Polynomial.Eval.Defs`. These supply the actual
  primitive definition, its shared local-field data and the polynomial API.
  Prior congruence theorems and level-field constructions are unnecessary
  to state the targets.
- Omitted the source proofs, unused `noncomputable section` and
  `open scoped Polynomial`; replaced the module documentation and adapted
  the declaration docstrings to describe targets.
- Disabled the unused-variable linter locally for each declaration to keep
  the explicit source hypothesis name `h`, whose proof is unused in the
  conclusion. This has no effect on the propositions.
- Added the dated modification notice and this paired Markdown.

No additional hypothesis, instance, axiom, local-field package or
polynomial definition is introduced.

## Attribution

The original copyright, Apache-2.0 release line and author header are
retained verbatim. The existing
[LICENSE](../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../licenses/NYLL/NOTICE) are reused unchanged.
Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
