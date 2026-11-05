# Actual full cubic sections on the original residue fibres

This derived construction specializes the full fibre-section basis to
the canonical cubic bundle of an ordinary polarized datum `a` over a
scheme `S`. The residue datum is the actual pullback
`a.pullback (S.fromSpecResidueField s)`. Both the coefficient field and
the source fibre use this original residue-point map.

`Datum.isIso_cubicBaseChangeEvaluation` retains the hypothesis that the
specified canonical `rigidificationBaseChangeMap b` is invertible, for
an arbitrary base morphism `b`. That map factors as the single-pullback
`baseChangeEvaluation` followed by the pushforward of the inverse of
`cubicBundlePullbackIso b`. The second factor is already an isomorphism.
Cancellation therefore proves that the first factor is invertible.
The lemma does not establish the retained canonical base-change
hypothesis.

Assume the actual cubic direct image `a.rigidificationModule` is
quasi-coherent. Choose a frame open `U` of size `m + 1`, assume `U` is
affine, and choose `s ∈ U`. Under the canonical base-change
invertibility hypothesis at `s`, `Datum.cubicFibreSectionBasis` is a
`Module.Basis` indexed by `Fin (m + 1)`, over `S.residueField s`, of
the entire relative global-section module of the cubic bundle of the
residue datum.

The definition starts with `fibreFullSectionBasis`, whose target is
the global sections of the single pullback of `a.cubicBundle`. It maps
this basis through the linear equivalence obtained by applying
relative global sections to the inverse of the specified
`cubicBundlePullbackIso`. Thus its target is the cubic bundle of the
actual pulled-back datum, rather than an unspecified isomorphic
bundle.

`Datum.cubicFibreSectionBasis_apply` identifies every basis entry with
`fibreFrameEvaluation`, acted on by that same inverse bundle comparison
on top sections. Its proof unfolds the transported basis and uses the
existing full-basis entry formula.

The following generation and map comparisons additionally retain
`EvaluationGenerates a.abelian.X.hom a.cubicBundle
(𝟙 a.rigidificationModule)`:

- `Datum.cubicFibreSectionBasis_generate` proves that the nonvanishing
  loci of these particular basis sections cover the source fibre.
  It transports the existing changed-evaluation generation result
  through the actual bundle isomorphism and uses the entry formula.
- `Datum.cubicFibreSectionBasis_coordinates` identifies their relative
  linear-system map with `fibreEvaluationCoordinates`. The proof uses
  invariance of the relative linear-system map under a bundle
  isomorphism and equality of the actual section families.
- `Datum.cubicFibreSectionBasis_toRelative` identifies the polynomial
  `Datum.cubicSectionMap` of the residue datum, followed by
  `RelativeProjectiveSpace.affineComparisonIso.hom`, with these same
  relative fibre coordinates. The implemented proof applies the
  coefficient-comparison theorem with the identity map of the original
  residue spectrum and cancels the inverse affine comparison.

For the remaining comparisons, assume `0 < d` and that the actual
direct image is locally free of rank `6 ^ g * d`. Use a frame of size
`cubicProjectiveDimension g d + 1`, which equals that rank.
`Datum.cubicProjectiveFibreChartIso` composes the affine projective
comparison with the existing `FrameBundle.fibreChartIso`. Its source
is polynomial projective space over the original residue field, and
its target is the actual fibre of `a.cubicProjectiveProjection`.

`Datum.cubicFibreSectionBasis_toEvaluationFibre` proves that the
polynomial full-basis section map, followed by this specified
isomorphism, is exactly `a.cubicProjectiveEvaluationFibre`. This is an
equality into the whole target fibre. The proof composes the preceding
relative-coordinate equality with the existing whole-fibre chart
comparison.

`Datum.isClosedImmersion_cubicFibreSectionBasis_iff` consequently
equates closed immersion of that full-basis section map with closed
immersion of the actual fibre evaluation. Its proof rewrites by the
map equality and cancels postcomposition with the chart isomorphism.
It retains every premise needed to construct the basis and both maps.

The provenance is internal and derived from the imported actual
section, bundle-comparison, projective-chart and linear-system
constructions. No new assertion from the literature is introduced.
Canonical cubic direct-image base change, quasi-coherence, the cubic
rank theorem, generation, fibre very ampleness, and representability
remain separate geometric obligations. In particular, the closed
immersion equivalence supplies no proof that either map is a closed
immersion, and this construction does not prove the host
`LargeLevelRepresentabilityStatement`.
