# Base change of finite vector-bundle series

This internal derived module preserves the exact finite-vector-bundle
predicate and finite normal series under any morphism of base schemes,
at arbitrary universe `u`. It imposes no flatness, affineness, nonemptiness,
or constant-rank hypothesis on the base change.

`IsFiniteLocallyFree.pullback` applies the first conjunct of the published
`Langlands.Scheme.Modules.pullbackFiniteLocalBasisRank`. That theorem
supplies one datum on the actual pullback which is both locally free
and finite type. It retains the original local basis indices over
inverse-image opens, with no need to choose a common rank.

`IsVectorBundleAdditive.baseChange` pulls back the same actual module sheaf.
Its point data and their precise relative-section naturality come from
`baseChangeSectionPointsEquiv` and
`baseChangeSectionPointsEquiv_naturality`, which use composition of actual
module pullback and the all-test point equivalence. Affineness and
smoothness are stable under the Cartesian base-change square.

`HasVectorBundleSeries.baseChange` preserves the supplied length by
induction. At length zero the all-test range and bottom subgroup commute
with base change, and the base-change functor sends the identity to the
identity. At positive length it pulls back both group schemes
and both maps in the first step. Closedness, smoothness, normality,
the represented fppf quotient, and the exact vector-bundle predicate
are preserved by their published base-change interfaces and the preceding
lemma. The induction hypothesis supplies the remaining series.
`HasFiniteVectorBundleSeries.baseChange` uses the same existential length.

The selected data definition `seriesWitnessBaseChange` transports a
subtype-valued length-and-proof witness, preserving its value projection
definitionally, as recorded by `seriesWitnessBaseChange_val`.

The proof is derived from the Library's finite local basis, actual
section-pullback, subgroup, and fppf quotient APIs. It does not construct
or descend a radical filtration and does not assert reflection of a
series from a cover.
