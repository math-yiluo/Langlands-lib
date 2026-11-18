# Refining a recognized target affinoid by target neighborhood families

This internal module is the first step toward the target-local finiteness
criterion `StrongHom.FiniteOverTargetLocalityStatement`. Field and
space/index universes stay independent. Everything here is a
combinatorial or topological refinement of the statement's hypothesis.
No finiteness is proved, and no descent is used.

## Generic chart refinements

- `IndexedAffinoidAtlas.exists_chart_finset_of_isQuasinet`: suppose the
  original charts contained in a subspace `Y` form a quasinet of `Y`. Then
  every point of `Y` has finitely many original charts contained in `Y`
  whose union contains `O ∩ Y` for some ambient neighborhood `O` of the
  point. The proof takes the finite quasinet family at the point and picks
  a chart for each of its members.
- `RecognizedSubset.isCompact_locus`: the locus of a recognized subset is
  compact, because it is the range of the continuous chart on a compact
  spectrum.
- `RecognizedSubset.exists_goodChart_finset_at`: fix a point `x` of a
  recognized subset `W` and a finite family `I` of recognized subsets. Each
  member of `I` contains `x` and satisfies a predicate `𝓕`, and the union
  of `I` is a neighborhood of `x`. Then finitely many original charts cover
  `O ∩ W.locus` for some neighborhood `O` of `x`, and each of these charts
  lies in `W.locus ∩ T.locus` for some member `T` satisfying `𝓕`. For each
  member `T`, the charts inside `W.locus ∩ T.locus` form a quasinet. This
  holds because the original chart family is a net and the
  contained-chart families of `W` and `T` are quasinets, so the previous
  lemma applies. The neighborhood is the union of `I` intersected with
  the finitely many neighborhoods obtained this way.
- `RecognizedSubset.exists_goodChart_finset`: if the previous hypothesis
  holds at every point of `W.locus`, compactness of `W.locus` gives one
  finite set of such good original charts covering `W.locus`.

## The family hypothesis and its refinements

The remaining declarations concern a strong morphism
`g : A.saturatedPresentation ⟶ B.saturatedPresentation` and subsets
`V ⊆ A.space` and `U ⊆ B.space`.

- `StrongHom.FiniteTargetMember g V U T` says three things about a
  recognized target affinoid `T`: `T.locus ⊆ U`; there is a recognized
  source subset `P` whose chart image lies in `T`'s chart range and whose
  locus is `V ∩ g⁻¹(T.locus)`; and the actual full-recognition pair
  pullback `g.fullRecognitionPairs.pullback P T h` is finite Banach.
- `StrongHom.HasFiniteTargetFamilies g V U` is copied verbatim from the
  family hypothesis of `FiniteOverTargetLocalityStatement`.
- `StrongHom.FamilyRefinement g V U W`, for a recognized target affinoid
  `W`, is a finite list of original saturated target charts `index k`
  covering `W.locus`. For each `k` it records a recognized target subset
  `target k ⊆ U` containing the chart, with the chart also inside
  `W.locus`. It also records a recognized source subset `left k` with
  locus `V ∩ g⁻¹((target k).locus)` and a finite Banach actual pair
  pullback.
- `HasFiniteTargetFamilies.exists_goodChart` and
  `HasFiniteTargetFamilies.refinement` build such a refinement, by choice,
  for every recognized target affinoid `W` with `W.locus ⊆ U`. They apply
  `exists_goodChart_finset` with `𝓕 = FiniteTargetMember g V U`.

## Finite local base-change models

For a refinement `F`:

- `F.domain k` is the refinement chart as an original full domain of `W`.
- `F.cover` is the resulting finite full-domain cover of the whole
  spectrum of `W`.
- `F.rightCover` is a `RecognizedOpenImageCover` for the identity strong
  morphism of `B`. Its targets are the family members `target k`, and its
  bounded maps are the original restrictions of `target k` to the
  refinement charts. The chart compatibility follows from the
  ambient-chart identities of original restrictions and original domains.
- `F.models` is a `FiniteOpenBaseChangeModels` package for the pair `g`
  and identity, whose finite left preimages are the supplied `left k`.
  This reuses the existing Library construction with the identity as
  second map. Its `algebraDescentData` is then the finite algebra descent
  datum of the local models over the cover of `W`, with no further
  hypothesis.

## Provenance

This is internal infrastructure. The topological part (finite chart
refinement from quasinets plus compactness) is standard. The packaging
reuses the Library's `FiniteOpenBaseChangeModels` interface.
