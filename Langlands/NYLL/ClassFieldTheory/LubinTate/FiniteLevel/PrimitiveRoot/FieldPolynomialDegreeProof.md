# Degree of the primitive polynomial over the base field (M341.006)

`Langlands.NYLL.LubinTate.standardLubinTatePrimitivePolynomialOverField_natDegree`
proves the fully applied imported target
`Langlands.NYLL.LubinTate.standardLubinTatePrimitivePolynomialOverField_natDegreeStatement F π n`.
For `q = Nat.card F.residueField`, this is

```lean
(standardLubinTatePrimitivePolynomialOverField F π n).natDegree =
  (q - 1) * q ^ n
```

The theorem retains independent universes `u v`, implicit
`{K : Type u} [Field K]`, and explicit
`(F : Langlands.NYLL.LocalFieldTheory.DiscreteValuationField.LocalField.{u,v} K)`
`(π : F.valuationSubring)` `(n : ℕ)`. It applies to every `π`; there is
no uniformizer or additional finiteness hypothesis.

## Implemented proof

Unfold the imported Prop target and the definition of
`standardLubinTatePrimitivePolynomialOverField`. The latter is the
valuation-ring primitive polynomial mapped along
`algebraMap F.valuationSubring K`. Apply `Polynomial.Monic.natDegree_map`
with the imported `standardLubinTatePrimitivePolynomial_monic F π n`
(M339.017), which preserves the natural degree under this coefficient
map because the polynomial is monic and the target field is nontrivial.
The imported `standardLubinTatePrimitivePolynomial_natDegree` (M339.016)
then gives `(q - 1) * q ^ n`.

The only new declaration is this exact proof. The target, definitions,
prerequisite proofs and their paired Markdown are imported without edits.

## Source and adaptations

Naganori Yamaguchi, NYLL ClassFieldTheory commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/PrimitiveRoot.lean`,
M341.006 lines 96–105 (statement 98–102, proof 103–105), with the
universe and variable context at lines 32–42. Source SHA-256:
`b9d4862f4873c982618ff0f591c73b251f7a6f6f3d4fc6e93134b6d4ecb732b4`.
The registered sources are `external-lean-reuse-snapshots-2026-10-21`
and `nyll-classfieldtheory-fbd320cd-supplement`.

Worker 554 extracted this single proof into the focused module,
prefixed the namespace and opened local-field namespace with
`Langlands.NYLL`, and replaced the source imports by the published target
and focused monicity and degree proof modules. The theorem type is the
fully applied imported Prop target; an initial unfold exposes its equality
for the source's three-rewrite proof. The universe parameters and complete
parameter telescope are preserved. The source's unused scoped polynomial
open is omitted. No other source theorem is included.

The original copyright, author and Apache-2.0 header are preserved.
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` retain the license and
attribution and are unchanged.
