# Coordinate maps into recognized affinoid algebras of an affine analytification

Lean module: `Langlands.Geometry.Analytic.FinitePieceLocalMaps`
(namespace `Langlands.Analytic.AffineAnalytification.FinitePieceLocal`). Support module for
the proof of `AffineAnalytificationFiniteGermComparisonStatement`.

## Content

Let `A` have a finite polynomial presentation `P` over a complete ultrametric nontrivially
normed field `K`. Let `W` be a recognized affinoid subset of the analytification of `A`.

* `recognized_algebra_ext`: elements of `W.algebra` agreeing under all original restrictions are
  equal (`componentCover.algebra_ext_of_restrict_eq`).
* `isCompact_recognized_locus`: `W.locus` is compact, being the image of the compact spectrum.
* `exists_orig_superset`: a compact set lies in all sufficiently large original saturated
  charts.
* `recMap P W j hW : A →ₐ[K] W.algebra`: the coordinate map, `satMap P j` followed by the
  restriction `W.containedRestriction j hW` from a saturated chart `j` whose range contains
  `W.locus`.
* `recMap_eq`: `recMap` does not depend on the chart `j`. Both choices have the same original
  restrictions (`originalRestriction_recMap`).
* `recMap_pointSeminorm`: for a point `t` of the Banach spectrum of `W.algebra`,
  `t (recMap a) = pointSeminorm K P (W.chart t) a`. It follows from the published
  `LocalDomainMaps.affinoidBaseMap_localAlgebraMap` and `pointSeminorm_affinoidBaseMap` together
  with `W.chart_containedRestriction`.
* `recMap_flat`: given `AffineAnalytificationChartFlatStatement` and
  `Domain.FlatnessStatement`, `recMap` is flat. It is the composite of the chart flatness map
  `A → chart algebra`, the domain of the saturated representative, and the contained domain
  `W.containedDomain j hW`. Each is flat, and flatness composes.
* `pullback_recMap`: the bounded map `φ` of a piece `(V', W)` satisfies
  `φ (recMap P W j a) = recMap Q V' i (f a)`. This uses the published
  `fullRecognitionPairs_comp_containedRestriction` and
  `LocalDomainMaps.saturatedHom_pullback_localAlgebraMap`.

## Provenance

Internal. `recMap` is the Library's version of the canonical map from an algebra to the algebra
of an affinoid domain of its analytification. Its point compatibility and its flatness are the
statements of Berkovich 1990, §3.4 (Theorem 3.4.1 and the last paragraph of its proof, printed
pp.63–64), reduced to the Library's chart and domain flatness statements. `FinitePieceLocalProof`
uses `recMap` for the witnesses `α` and `β` of `AffineAnalytificationFinitePieceLocalStatement`.
