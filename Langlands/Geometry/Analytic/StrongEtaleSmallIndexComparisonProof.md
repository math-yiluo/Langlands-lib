# Proof: étale recognition for small-index affine analytic presentations

The theorem
`Langlands.Analytic.SaturatedAtlasPresentation.strongEtaleSmallIndexComparison`
proves the unchanged proposition
`Langlands.Analytic.SaturatedAtlasPresentation.StrongEtaleSmallIndexComparisonStatement.{u}`
of `StrongEtaleSmallIndexComparisonStatement`. Its module is
`Langlands.Geometry.Analytic.StrongEtaleSmallIndexComparisonProof`.

Let `K : Type u` be a complete, ultrametric, nontrivially normed field and let
`P Q : AffinoidAtlasPresentation.{u, u, 0} K`. For every strong map
`f : ofSaturation P ⟶ ofSaturation Q` that is étale over all recognized
pieces of the original presentations, `StrongHom.IsEtaleAllPieces (A := P)
(B := Q) f`, the theorem proves `strongEtale f`. The map `f`, its continuous
map and all its bounded pullbacks are the given ones; nothing is reindexed or
replaced.

## A comparison in every index universe

The module first proves
`strongEtale_ofSaturation_iff_isEtaleAllPieces`: for
`P Q : AffinoidAtlasPresentation.{u, v, w} K` with independent universes and
any `f : ofSaturation P ⟶ ofSaturation Q`,

```text
strongEtale f ↔ StrongHom.IsEtaleAllPieces (A := P) (B := Q) f.
```

The published `strongEtale_ofSaturation_iff` in `SaturatedEtaleComparison`
states this when the index universe equals the space universe. The target
theorem is the direction `←` at `v = u` and `w = 0`.

## Implemented proof

Two helper modules supply the argument.

1. `SaturatedRecognizedPieces` restates the all-pieces predicate on objects of
   the saturated category: `IsEtaleOnRecognizedPieces g` for
   `g : StrongHom S.presentation T.presentation`. By
   `StrongHom.isEtaleAllPieces_iff_isEtaleOnRecognizedPieces`, proved by
   `rfl`, `StrongHom.IsEtaleAllPieces (A := P) (B := Q) g` is
   `IsEtaleOnRecognizedPieces g` for `S = ofSaturation P` and
   `T = ofSaturation Q`, in every universe. Thus the all-pieces predicate
   depends on `P` and `Q` only through their constructed saturations.
2. `SaturatedAtlasIdempotence` proves
   `ofSaturation_saturatedPresentation`: `ofSaturation P.saturatedPresentation`
   and `ofSaturation P` are the same object of the saturated category, because
   saturating a saturated atlas returns literally the same atlas.

Apply the published `strongEtale_ofSaturation_iff` to the presentations
`P.saturatedPresentation` and `Q.saturatedPresentation`. Their chart indices
are in the universe of their spaces, so it applies whatever the universe of
the original indices. For every
`g : ofSaturation P.saturatedPresentation ⟶ ofSaturation Q.saturatedPresentation`
it gives `strongEtale g ↔ StrongHom.IsEtaleAllPieces
(A := P.saturatedPresentation) (B := Q.saturatedPresentation) g`, and by step
1 the right side is `IsEtaleOnRecognizedPieces g`. This statement concerns
only the two objects `ofSaturation P.saturatedPresentation` and
`ofSaturation Q.saturatedPresentation`. Rewriting them along the two equalities
of step 2 gives, for every `g : ofSaturation P ⟶ ofSaturation Q`,
`strongEtale g ↔ IsEtaleOnRecognizedPieces g`. A last application of step 1,
now to `P` and `Q`, gives the comparison. The rewriting is a substitution of
equal objects of one category: the predicate `strongEtale` and the morphism
`f` are not changed.

The proof uses only `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The geometric source of the étale condition is Berkovich, *Étale cohomology
for non-Archimedean analytic spaces* (1993), Proposition 3.2.3 (printed p.58 /
PDF p.55) and Definition 3.3.4 (printed p.63 / PDF p.60), with the quotations
and locators recorded in `FullRecognitionEtaleComposition.md`. The universe comparison
is internal to the Library's atlas implementation, and the proof is derived:
it combines the published equal-index comparison with the idempotence of the
Library's local-domain saturation. It does not follow a source argument.
