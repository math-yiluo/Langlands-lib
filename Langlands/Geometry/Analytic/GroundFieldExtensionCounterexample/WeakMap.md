# A strong atlas map twisted by Frobenius on some target charts

This module constructs `weakMap`, a `StrongHom` over `F₂` (trivial norm) between
two affinoid atlas presentations. Its pullbacks on two incomparable target charts
differ by the Frobenius endomorphism of the source algebra. Over `F₂` this twist
is invisible on spectra, so all the axioms of `StrongHom` hold. After the ground
field extension to `F₄`, the twist moves points. This is why a `StrongHom` need
not extend along a ground field extension. All declarations are in the namespace
`Langlands.Analytic.GroundFieldExtensionCounterexample`.

This module contains only the construction. The statement that `weakMap` does not
extend is `NonExtensionStatement`, proved by `nonExtension` in
`GroundFieldExtensionCounterexample/NonExtensionProof`. It uses the ground field
extension of affinoid atlas presentations from module `GroundFieldExtensionAtlas`.
In outline, that statement says that the two atlas presentations
extended to `F₄` admit no `StrongHom` whose pullbacks are the ground field
extensions of the pullbacks of `weakMap`. Nothing about `F₄`-base change is
stated or proved here.

## Provenance

This is an internal construction: the counterexample with K = F2 with the
trivial norm, L = F = F4, the two incomparable triple charts, and Frobenius on
one of them. It is the reason why the ground field extension of atlas maps in
`GroundFieldExtensionMaps` extends only `CompatibleStrongHom`s, not arbitrary
`StrongHom`s, and it records that a weak `StrongHom` need not extend along a
ground field extension. There is no literature source. The
Library notions used are:

- `StrongHom` (module `StrongAtlasMaps`);
- the atlas of all rational charts `RationalSpectrumAtlas.atlas` (module
  `RationalSpectrumAtlas`);
- `AffinoidAtlasPresentation.subpresentation` with
  `IndexedAffinoidAtlas.IsLocallyRefiningSelection` (module `AtlasSubatlas`);
- the one-chart presentation `PresentedAffinoidSpace.atlasPresentation` (module
  `AffinoidSpectrumAtlas`);
- `RationalChart.upperBound` and `RationalChart.mem_locus_upperBound` (module
  `GeneralizedAffinoid/RationalLaurentNeighborhoods`);
- `RationalChart.existsUnique_factorization` (module
  `GeneralizedAffinoid/RationalRepresentationProof`).

The algebras `sourceAlgebra ≅ F₄ × F₄` and `targetAlgebra ≅ F₄⁴`, the map
`restrictMap`, `frobenius`, `ι = targetInclusion` and the factor points come
from `GroundFieldExtensionCounterexample/Charts`.

## Rational domains of the target spectrum

- `idempotent p := Pi.single p 1` is the idempotent of `F₄⁴` supported on the
  factor `p`, and `idempotent_apply` computes its entries.
- `upperChart a` is the rational chart `RationalChart.upperBound (ι a) (1/2)` of
  `targetAlgebra`. Its locus is `{y | y (ι a) ≤ 1/2}`. Points take only the
  values `0` and `1`, so `mem_upperChart_locus` shows that this locus is the
  vanishing locus `{y | y (ι a) = 0}`.
- `leftDomain` is the locus of `upperChart (idempotent 3)`, and `rightDomain`
  is the locus of `upperChart (idempotent 2)`. These are the two triple charts.
  Informally, `M(F₄⁴)` consists of the four factor points. Then `leftDomain` is
  the set of points of the factors `0, 1, 2`, and `rightDomain` is the set of
  points of the factors `0, 1, 3`. The Lean development uses only the
  vanishing-locus descriptions. It does not prove that the spectrum has
  exactly four points or that the two domains are incomparable.
- `pointDomain p` is the locus of `upperChart (1 - idempotent p)`.
- `sourceImage` is the image of the map of spectra induced by `restrictMap`.
  `comap_restrictMap_apply` evaluates image points on `ι`-values.

The following facts are proved:

- `sourceImage_subset_upperChart`, `sourceImage_subset_leftDomain`,
  `sourceImage_subset_rightDomain`: the source image lies in both triple
  charts, because `restrict` kills `idempotent 2` and `idempotent 3`
  (`restrict_idempotent`).
- `pointDomain_subset_upperChart` and `pointDomain_subset_left_or_right`: each
  `pointDomain p` lies in `leftDomain` (if `p ≠ 3`) or in `rightDomain` (if
  `p = 3`). The proof uses `idempotent_mul_one_sub`.
- `not_sourceImage_subset_pointDomain`: no `pointDomain p` contains the source
  image. Given `p`, choose `q : Fin 2` whose image in `Fin 4` differs from `p`.
  The image of `sourcePoint q` takes the value `1` at `ι (1 - idempotent p)`,
  so it is not in `pointDomain p`.
- `exists_mem_pointDomain`: every point lies in some `pointDomain p`, since
  `∏ p (1 - idempotent p) = 0`.
- `mem_pointDomain_iff_lt` and `isOpen_pointDomain`: `pointDomain p` is the
  strict sublevel set `{y | y (ι (1 - idempotent p)) < 1/2}`, so it is open.

## The two atlas presentations

`IsSelected i` holds for a rational chart `i` of `targetAlgebra` if both:

- the locus `i.val` lies in `leftDomain` or in `rightDomain`; and
- it is not the case that `i.val` contains `sourceImage` and also lies in
  `leftDomain ∩ rightDomain`.

`isSelected_of_subset_pointDomain` shows that every chart inside some
`pointDomain p` is selected. `isLocallyRefiningSelection` proves the Library's
condition `IsLocallyRefiningSelection` for the atlas of all rational charts.
Take a rational chart `U`, a point `y ∈ U` and `p` with `y ∈ pointDomain p`. The
single selected chart `U ∩ pointDomain p` (`RationalSpectrumAtlas.Index.inter`)
lies in `U`, contains `y`, and is a neighbourhood of `y` within `U` because
`pointDomain p` is open. `range_atlas_chart` identifies chart images with loci.

- `targetAtlasPresentation : AffinoidAtlasPresentation.{0, 0, 0} F₂` is the
  subpresentation of `⟨BanachSpectrum targetAlgebra, RationalSpectrumAtlas.atlas
  targetAlgebra⟩` given by `IsSelected`. Its space is the whole spectrum of
  `targetAlgebra`.
- `sourceAtlasPresentation : AffinoidAtlasPresentation.{0, 0, 0} F₂` is
  `PresentedAffinoidSpace.atlasPresentation (op sourceAlgebra)`: the spectrum of
  `sourceAlgebra` with its one chart.

## The twisted strong map

- `weakBaseMap` is `BanachSpectrum.comapContinuous` of `restrictMap`. By
  `image_weakBaseMap`, the image of the unique source chart is `sourceImage`.
  So by `admissible_iff`, a pair consisting of the source chart and a target
  chart `j` is admissible exactly when `sourceImage ⊆ j.val.val`.
  `range_targetAtlasPresentation_chart` and `val_subset_of_range_subset`
  translate between chart images and loci in the selected atlas.
- `factor j h` is the unique bounded `F₂`-algebra map `ψ` from the chart algebra
  of a rational chart `j` containing `sourceImage` to `sourceAlgebra` with
  `ψ ∘ baseMap = restrictMap`. It comes from
  `RationalChart.existsUnique_factorization`, applied via
  `hasImageIn_of_subset`. Its properties are `factor_comp_baseMap`,
  `factor_eq_of_comp_baseMap`, and `factor_restriction`, which says that the
  factorizations are compatible with the rational restriction maps.
- `weakPullback j h` is `frobenius ∘ factor j h` if `j.val ⊆ rightDomain`, and
  `factor j h` otherwise (`weakPullback_of_subset`,
  `weakPullback_of_not_subset`).
- `apply_frobenius` and `apply_weakPullback_baseMap`: every point `x` of the
  source spectrum satisfies `x (weakPullback j h (baseMap a)) = x (restrictMap
  a)`. This holds because `frobenius` fixes every point (`comap_frobenius`).
- `subset_rightDomain_iff`: let `j ⊆ j'` be selected charts and suppose the
  smaller one, `j`, contains `sourceImage`. Then `j` lies in `rightDomain`
  exactly when `j'` does. Suppose `j ⊆ rightDomain` but `j'` does not lie in
  `rightDomain`. Then `j'` is selected, so it lies in `leftDomain`. Now `j`
  contains `sourceImage` and lies in `leftDomain ∩ rightDomain`, so `j` is not
  selected, a contradiction. This is the only place where the exclusion clause
  of `IsSelected` is used.

`weakMap : StrongHom sourceAtlasPresentation targetAtlasPresentation` has base
map `weakBaseMap` and pullbacks `weakPullback`.

- `target_exists`: the chart `leftDomain` (`ofChart (upperChart (idempotent 3))`)
  is selected and admissible. `targetPoint 2` lies in `leftDomain` but not in
  `rightDomain`, so `leftDomain ⊄ leftDomain ∩ rightDomain`.
- `chart_comm`: both sides are points of the target spectrum. They agree on every
  element `a` by `apply_weakPullback_baseMap`.
- `restriction_comm`: the source has a single chart and its restriction is the
  identity. So this axiom reduces to `weakPullback j' = weakPullback j ∘
  restriction j j'` for admissible selected `j ⊆ j'`. By
  `subset_rightDomain_iff`, `j` and `j'` are either both twisted or both
  untwisted. The equation then follows from `factor_restriction`.

Informally, the twist is visible in the selected atlas. The chart `leftDomain`
is untwisted and the chart `rightDomain` is twisted. Both contain the source
image. No selected chart contains the source image and lies in both, so there is
no admissible chart below both of them that would force the two pullbacks to
agree. The Library's `CompatibleStrongHom` additionally requires
`StrongHom.HasLocallyCompatiblePullbacks`. That condition compares the
pullbacks for two admissible target charts on local domains inside their
intersection. `weakMap` is designed so that this comparison fails for
`leftDomain` and `rightDomain`. The Lean development neither states nor proves
that `weakMap` fails to be a `CompatibleStrongHom`.
