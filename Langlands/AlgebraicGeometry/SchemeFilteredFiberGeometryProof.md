# Filtered descent of geometric fibre properties

`Langlands.AlgebraicGeometry.SchemeLimitModel.finitePresentationInitialRingFiberGeometryDescent`
proves the unchanged published proposition
`FinitePresentationInitialRingFiberGeometryDescent.{u}`. For every natural
dimension `d`, two finitely presented scheme models over an original stage
of a small filtered ring diagram, and a morphism between them, it equates
the required fibre property over the colimit with its occurrence after
some original outgoing transition.

The property is nonemptiness, geometric connectedness and componentwise
pure dimension `d` of every actual residue-field fibre. Both model
structure maps are locally of finite presentation, quasi-compact and
quasi-separated. The conclusion retains arbitrary universe `u`,
noninjective ring transitions, and nonaffine and nonseparated models.
It adds no properness, smoothness, flatness or Noetherianity assumption.

This is the last property clause of Brian Conrad, *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), printed pp. 5–6,
Theorem 3.4(2). The registered original source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The extension from directed posets to small filtered categories uses the
published under-category construction and keeps its chosen outgoing
arrow. The implemented proof combines published constructibility and
limit results; Conrad's proof refers to EGA for this property clause.
Worker 105 authored the shared conditional assembly. Worker 1483
completed it using the published prerequisite proofs and prepared this
focused proof pair.

The first lemmas prove that the pure-dimension fibre locus commutes with
an actual cartesian base change, using
`hasPureDimension_locallyFiniteType_fiberBaseChange_iff` from the published
`SchemePureDimensionProof`. Intersecting this equality with the published
geometric-connectedness comparison gives the same equality for the
combined locus. Geometric connectedness already includes nonemptiness.
These comparisons specialize to the actual model maps, transition
squares and cone legs from `SchemeLimitFiberLoci`. They require no limit
witness.

For a cofiltered diagram with affine transitions and quasi-compact
quasi-separated stages, the proof then assumes that the combined locus
is constructible at every target model stage. If its pullback to the
limit is the whole target, the published
`exists_map_preimage_eq_univ_of_isConstructible` produces an incoming
stage where its pullback is the whole target. The cartesian transition
comparison identifies that pullback with the incoming stage's combined
fibre locus. Fullness of this locus is exactly the required all-fibres
condition. Conversely, fullness at any stage pulls back to fullness at
the limit by the cone comparison.

The next reduction supplies constructibility at each stage. The
relative map is locally finitely presented, quasi-compact and
quasi-separated, and these properties persist in its actual cartesian
base changes. Each target model stage is quasi-compact and
quasi-separated. The geometric-connectedness constructibility theorem
therefore gives a constructible locus. For pure dimension, the published
sublevel properties give openness and retrocompactness of every
relative local-dimension sublevel. The helpers in
`RelativeDimensionSublevelStatement` express dimension unequal to `d`
by Boolean combinations of consecutive sublevels (with a separate
zero case). Chevalley's theorem and the complement of the image of
this exceptional source set give the constructible componentwise
pure-dimension fibre locus. Intersecting the two loci supplies the
constructible locus used by the limit argument.

The resulting equivalence is specialized first to the actual spectrum
diagram of a filtered algebra colimit, then to the algebra diagram on
the under-category of the specified original ring stage `j₀`. The
published tail-colimit comparison supplies the colimit witness and
identifies the base maps with `Spec.map (c.ι.app j₀)` and exactly
`Spec.map (F.map j.hom)` for `j : Under j₀`.

Finally, local finite presentation, quasi-compactness and
quasi-separatedness of the relative map follow from the two models:
its composite with the target structure map equals the source
structure map. The final theorem discharges both constructibility
premises with the published unconditional theorems
`geometricallyConnectedFiberLocalConstructibility` and
`relativeDimensionSublevelProperties_proof`. Thus no constructibility
premise remains in the endpoint.

This proof covers the specified fibre-property clause. The other
clauses of Theorem 3.4 and the remaining whole-paper obligations belong
to the parent task.
