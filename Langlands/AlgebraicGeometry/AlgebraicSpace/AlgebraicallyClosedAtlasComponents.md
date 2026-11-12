# Atlas components under field extension

This internal supporting construction compares actual connected-component sets
before and after represented field extension. It uses the Library's quotient
point sets and `pointTopology` explicitly. It does not change the host
constructibility statement.

`productAtlasCoverSets_eq_preimage` identifies the inverse image of a range in
the product chart with the inverse image, under `Over.prodLeftIsoPullback`, of
the actual field-base-change subscheme range. The proof applies the comparison's
first-projection equation to each point. No finiteness, closedness or
connectedness assumption is needed for this set equality.

`isConnected_productAtlasCoverSets` assumes the covering piece's composite
structure map is geometrically connected. The published theorem
`isConnected_fieldBaseChangeSubschemeRanges` supplies connectedness after any
field extension, and the comparison homeomorphism transfers it to the product
chart. Connectedness here includes nonemptiness.

`fieldAtlasClosedCoverComponentsEquiv` assumes a presheaf on schemes over
`Spec K`, a surjective etale scheme chart, and a finite family of closed
immersions into the chart whose ranges cover it and whose composite structure
maps are geometrically connected. For every scheme morphism `Spec L → Spec K`
between field spectra, it constructs an equivalence from the connected
components of the product of the presheaf with the represented `Spec L` to the
connected components of the original presheaf. Both sides use the actual point
topology.

The original ranges are connected because their source schemes are connected.
Their inverse images in the product chart are connected by the preceding
lemma and still cover that chart. Each remains closed by continuity of the
projection. The published product-atlas incidence formula identifies incidence
after base change with an original kernel-pair point whose base image lies in
the range of `Spec L → Spec K`. This range is the whole field spectrum, so the
incidence relations agree. The equivalence is the composite of the two actual
closed-cover component equivalences and `Quot.congr` on their common finite
label set. The index set may be empty. This construction needs no
quasi-separatedness of the presheaf and no finite-type assumption on the chart.

`algebraicallyClosedAtlasComponentsEquiv` assumes in addition that `K` is
algebraically closed and that the chart structure map is locally of finite type
and quasi-compact; it requires no supplied closed cover. The chart is then
Noetherian and has finitely many irreducible components. Take the vanishing-ideal
subschemes of these actual closed components. Their ranges are precisely the
components and cover the chart. Their source schemes are connected, by the
closed-embedding homeomorphisms with those ranges. Their composite maps to
`Spec K` are locally of finite type, so the published theorem
`Langlands.AlgebraicGeometry.algClosedConnected` makes each geometrically
connected. The preceding finite-cover construction gives the desired
equivalence for every field extension.

The unit is derived internally from the named published scheme-base-change,
connectedness, and atlas-incidence results. It is not a transcription of an
external source. It proves field-extension invariance over an algebraically
closed base in the represented-product model. Comparing relative presheaves on
different base categories, descending generic constancy from a splitting cover,
Noetherian induction and arbitrary-ring approximation remain outside its scope.
