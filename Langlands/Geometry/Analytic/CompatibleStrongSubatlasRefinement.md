# Compatible strong refinement squares for selected target atlases

This module places the constructed source refinement for a selected target
subatlas in the category of compatible strong maps. It constructs the
compatible inclusions and lift, proves equality of the full composites, and
records the resulting categorical commutative square.

## Hypotheses and provenance

The field `K` is a complete ultrametric normed field; trivial valuations are
included. The ambient universe is `v`, and the chart-index universe `w` is
independent. Objects are the existing actual affinoid atlas presentations.
A `CompatibleStrongHom A B` contains an actual continuous map, bounded
pullbacks for every admissible original chart pair, their structural equations,
and the intrinsic local compatibility law on those original bounded maps.
`CompatibleStrongMaps.hasLocallyCompatiblePullbacks_iff` identifies that law
with `HasCoherentPullbacks`, which tests all presented-affinoid coefficients
through every common original target subchart.

For the source-refined lift, the source satisfies
`ha : A.atlas.HasAllLocalDomains` and the target selection satisfies
`hP : B.atlas.IsLocallyRefiningSelection P`. The former says that each ambient
locus of a full local domain is the range of an original source chart; the
constructed saturated atlas has this property. The latter says that inside
each original target chart, at each point, a finite family of selected charts
contained in that chart and containing the point has a relative-neighborhood
union. Neither premise assumes the square or its source selection.

This is internal content, with no new external-literature assertion.
`StrongSubatlasSourceRefinement` constructs the source selection and lift from
actual inverse-image affinoid domains, source domain closure, and continuity.
`CoherentStrongChartChange` supplies the original all-coefficient law and its
identity example. `CompatibleStrongMaps` supplies its equivalence with local
compatibility. `CoherentStrongComposition` and `CompatibleStrongCategory`
construct composition and prove recovery of complete bounded composites and
full coherent extensionality. `StrongAtlasQuasiIsomorphisms` proves that the
actual subatlas inclusions are full quasi-isomorphisms. This module transfers
these original laws to selected indices and computes both actual composites.

## Compatibility on selected original charts

`StrongHom.hasCoherentPullbacks_restrictSubatlasSource` restricts any coherent
strong map to a locally refining source selection. Every new source index is
an original index with its selection proof, so the original coherence law at
`i.val` supplies the entire required coefficient test.

`StrongHom.hasCoherentPullbacks_targetSubatlasLift` proves the corresponding law
for the constructed source-refined lift into the selected target. It applies
the original law at `i.val`, `j.val`, and `k.val`, and uses `m.val` for the
selected common target test chart. The coefficient algebra and every bounded
test map remain unchanged. This uses only tests already covered by the
original law.

`compatibleSubatlasInclusion` upgrades the existing strong inclusion of any
locally refining subatlas. Its underlying strong map is exactly
`strongSubatlasInclusion`, its ambient map is the identity, and its pullbacks
are the actual original atlas restrictions. The original identity map is
coherent; the source-restriction result and the equivalence with local
compatibility provide the new field. No domain-closure premise is needed for
this inclusion. `isQuasiIso_compatibleSubatlasInclusion` retains the existing
full quasi-isomorphism theorem.

## The actual compatible source restriction and lift

`CompatibleStrongHom.restrictSubatlasSource` restricts a compatible map to any
locally refining original source selection. Its ambient map is exactly
`f.baseMap`, and at each admissible pair its bounded pullback is exactly
`f.pullback i.val j h`. Its compatibility follows from the source-restriction
coherence result.

For the source-refined lift, set

```text
Q i := exists j, P j and f.baseMap '' range (A.atlas.chart i)
                              is contained in range (B.atlas.chart j).
```

The imported `sourceSelectionForTarget_locallyRefining ha P hP` proves that
`Q` is locally refining. Its proof uses actual inverse-image domains and
pointwise finite relative neighborhoods. The resulting
`f.toStrongHom.targetSubatlasSource ha P hP` is the same-space presentation
`A.subpresentation Q hQ`.

`CompatibleStrongHom.targetSubatlasLift` has that source and target
`B.subpresentation P hP`. Its underlying strong map is exactly the imported
constructed lift. Its ambient map is exactly `f.baseMap`, and every admissible
bounded pullback is exactly `f.pullback i.val j.val h`. The preceding coherence
transfer supplies compatibility without replacing any of these maps.

## Equality of the full composites

`subatlasInclusion_comp` identifies the composite of the compatible source
inclusion with `f` as the entire compatible source restriction. The proof uses
`ext_of_pullback`: after the definitional ambient-map equality, it chooses one
admissible target for each source chart and computes that complete bounded
pullback by `comp_pullback`. The intermediate inclusion pullback is the
original self-restriction. The atlas identity equation and the bounded-map
identity law give the required equality.

`targetSubatlasLift_comp_inclusion` identifies the other route as the same
entire source restriction. For a selected source index, its property chooses
a selected target chart `j`. The proof computes the complete bounded composite
through that selected chart. The target inclusion contributes the original
self-restriction at `j`; the atlas identity equation and bounded-map identity
law reduce the result to `f.pullback i.val j h`. Full coherent extensionality
then identifies all other admissible pullbacks as well.

`targetSubatlasLift_square` combines these two equalities. If `s` and `t` are
the source and target compatible inclusions and `f'` is the constructed lift,
its equation is `f'.comp t = s.comp f`. This is equality in
`CompatibleStrongHom`, including the complete bounded families. No equality
of bounded maps is inferred merely from equality on spectrum points.

## The categorical square and quasi-isomorphisms

`CompatibleAtlasPresentation.targetSubatlas_commSq` records the same equation
as an actual `CategoryTheory.CommSq` in the existing category
`CompatibleAtlasPresentation K`. Its top arrow is the constructed lift, its
left and right arrows are the source and target compatible inclusions, and
its bottom arrow is `f`. Both vertical arrows are full quasi-isomorphisms by
`isQuasiIso_compatibleSubatlasInclusion` applied to their proved local
refinement conditions.

`CompatibleStrongHom.isQuasiIso_targetSubatlasLift` also proves that the lift
is a full quasi-isomorphism whenever `f` is one. It retains the imported
ambient homeomorphism and full affinoid-test representations on the selected
chart pairs.

## Scope

This unit constructs the actual compatible refinement square for a locally
refining original target subatlas and a source closed under all local full
domains. It assumes no global finite chart cover, directedness, or
upper-cofinality. Arbitrary target quasi-isomorphism squares, localization or
identification of the full analytic category, analytic and equivariant sites,
and Harris tower specializations remain obligations of the broader task.
