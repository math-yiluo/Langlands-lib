# Primitive division polynomial over the base field (M341.003)

`Langlands.NYLL.LubinTate.standardLubinTatePrimitivePolynomialOverField`
is the field-coefficient form of the level-`n + 1` primitive division
polynomial. It has independent universes `u v`, implicit
`{K : Type u} [Field K]`, explicit
`F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K`,
explicit `π : F.valuationSubring` and explicit `n : ℕ`, and returns
`Polynomial K`. Its body is

```lean
(standardLubinTatePrimitivePolynomial F π n).map
  (algebraMap F.valuationSubring K)
```

so it applies `Polynomial.map` to the published valuation-ring polynomial
`Langlands.NYLL.LubinTate.standardLubinTatePrimitivePolynomial F π n`
(M339.014),
namely `f^[n](X) ^ (q - 1) + C π` with `f = X ^ q + π X` and
`q = Nat.card F.residueField`. The coefficient map is Mathlib's
`algebraMap` for the canonical `Algebra` instance of a valuation subring
in its field. `F.valuationSubring` is the carrier of the chosen valuation's
`valuationSubring`, so this map is the inclusion of that subring into `K`.
No new valuation, separable closure or algebra structure is chosen here.

No uniformizer hypothesis is assumed, as in the source: the definition makes
sense for every element `π` of the valuation ring. Monicity, degree,
irreducibility (for a uniformizer), separability and root properties are
separate targets or later units; this pair proves none of them.

The source formula theorem M341.004 (lines 79–88) is not included. Its
equality
`standardLubinTatePrimitivePolynomialOverField F π n =
(standardLubinTatePolynomialIterate F π n).map (algebraMap F.valuationSubring K)
^ (Nat.card F.residueField - 1) + Polynomial.C (π : K)` is proved in the
source by `simp` unfolding this definition and
`standardLubinTatePrimitivePolynomial`; this pair supplies no such lemma.

## Original source and modifications

Naganori Yamaguchi, NYLL ClassFieldTheory commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveRoot.lean`, M341.003,
lines 71–77 (docstring 71–72, declaration 73–77); universe and variable
context at lines 32–42. Source file SHA-256:
`b9d4862f4873c982618ff0f591c73b251f7a6f6f3d4fc6e93134b6d4ecb732b4`.
Registered sources `external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and
`nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

The declaration name, universes, binder order and explicitness, return type
and body are those of the source. Worker 421 made these changes:

- prefixed the namespace `LubinTate` and the opened namespace
  `LocalFieldTheory.DiscreteValuationField` with `Langlands.NYLL`;
- extracted only M341.003 into this focused module, with a new module
  docstring and a modification note in the header;
- replaced the source imports (`PrimitiveEisenstein`, `IsSepClosed`,
  `GaussLemma`, `Cardinal.Finite`) by the single Library module
  `Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial.Primitive.Definitions`,
  which supplies the shared `LocalField` package and the published
  primitive division polynomial (M339.014) and transitively brings
  Mathlib's polynomial `map`/`algebraMap` interfaces.

The source's `noncomputable section`, `open scoped Polynomial`, universe
declaration and `variable {K : Type u} [Field K]` are retained.

The original copyright, Apache-2.0 release line and author line remain in the
Lean header. Apache-2.0 licensing and attribution are retained in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`, which this pair does not
modify. The source file is not among the Anthropic FLT-derived files listed
in the supplement's `Nyll/ClassFieldTheory/ANTHROPIC_FLT_SOURCE.md`.
