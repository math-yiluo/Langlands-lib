# Simply connected chamber stabilizers over the maximal unramified extension

`Langlands.Geometry.Building.MaximalUnramified.simplyConnectedChamberStabilizer`
proves the unchanged published proposition
`Langlands.Geometry.Building.MaximalUnramified.SimplyConnectedChamberStabilizerStatement.{u}`
at arbitrary universe `u`, with no additional premises.

For every original nonarchimedean local field `F`, every affine simply connected
group `G` over `K = inertiaFixedField F`, every supplied
`C : MaximalUnramified.BuildingData F G`, every chamber `Y` of its reduced
building, and every `g : rationalPoints G` with `(g • ·) '' Y = Y`, the conclusion
is `g ∈ C.pointwiseFixer Y`.

The proof applies `simplyConnectedChamberStabilizerReduction` to the published
unconditional theorem `simplyConnectedNormalizerAffineWeyl`. The latter identifies
the image of the full original normalizer action on the apartment of the same
datum `C` with the affine Weyl group of `C.affineRoots`. Its implementation uses
quasi-splitness over the actual maximal unramified field and rational root
generation for quasi-split simply connected groups.

The accompanying reduction first treats any integer-valued building datum whose
normalizer image is contained in its affine Weyl group. Its affine roots form
a locally finite reflection arrangement by the proved integer-valued root
geometry. Thus `AffineRootSystem.affineWeyl_facet_fixing` fixes each apartment
facet preserved by a normalizer element pointwise.

For a translated apartment facet in the reduced quotient,
`exists_normalizer_stabilizes_eq_on_translated_facet` supplies a normalizer
element preserving the original facet and agreeing with the translated
stabilizer action there. Pointwise fixing in the apartment therefore gives
pointwise fixing in the quotient. A chamber is a facet, so this applies to `Y`.
The published normalizer equality supplies the required containment.

This internal composition proves the original target for every supplied `C`,
including rank zero and groups over `K` that do not descend to `F`. It assumes
no additional normalizer-image, apartment-comparison or chamber-fixing
proposition. The original target pair and its imports are unchanged. The source
comparison with Kaletha–Prasad 4.1.12(1), Remark 4.1.13 and 9.3.26 remains in the
target's Markdown; this proof establishes the result directly from the supplied
data and the imported theorems.
