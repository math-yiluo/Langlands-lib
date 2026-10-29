# The JPSS two-block Whittaker extension formula

Author: Worker 643.

`Langlands.Whittaker.twoBlockWhittakerExtension.{uF,uV₁,uV₂}` proves exactly
the closed published proposition
[`TwoBlockWhittakerExtensionStatement`](TwoBlockExtensionStatement.md).
The field universe and the two representation carrier universes remain
independent.

For ranks `A = a+1` and `B = b+1`, the conclusion extends every actual
Whittaker coefficient `W₂` of the second block and every Schwartz–Bruhat
row cutoff `Φ` to an actual Whittaker coefficient `W` of the canonical
normalized upper induction in the ordered blocks `(π₁,π₂)`, with

```text
W(diag(g,I_A)) = W₂(g) * Φ(lastRow(g)) * |det(g)|^(A/2).
```

The target's literal conjugations on `ULift.{uV₂} V₁` and
`ULift.{uV₁} V₂`, its entry-preserving rank transport, its leading `B`
coordinates, and its positive real determinant half power are retained.
The coefficient belongs to the published intrinsic `whittakerSet` of the
actual induction.

## Implemented proof

Apply the published
[`twoBlockWhittakerExtension_of_rowFourierSurjectivity`](TwoBlockExtensionAssemblyProof.md).
Its conclusion is the exact target above. Its premise is row Fourier
surjectivity for every prime, every p-adic field in universe `uF` with its
canonical topological data, and every natural row dimension.

For each of those inputs, apply
[`HarmonicAnalysis.padicRowFourierSurjectivity`](../../HarmonicAnalysis/PadicRowFourierSurjectivityProof.md)
to `F`, `F.canonicalTopologicalData`, and `d`. That theorem holds for every
supplied topological realization and every scalar additive Haar measure.
Specializing it therefore discharges the entire premise, including its
character, measure and cutoff quantifiers.

The imported extension assembly supplies the open-cell coefficient
construction, functional transport through the literal carrier lifts,
normalization of the first functional, the matrix Fourier slice, the
leading-embedding identity, and the determinant calculation. Its
coefficient construction uses the given factors and their functionals
directly, so it applies to the target's Whittaker-type scope, including
reducible factors. The final theorem has no additional hypotheses and
requires no supplied measure or induced Whittaker functional.

## Provenance

This final proof is an internal composition of the two imported Library
theorems. The original JPSS Proposition 9.1 interpretation and conventions
are documented in the unchanged target pair; this file adds no separate
literature claim. The target pair and all existing imported pairs are
preserved.
