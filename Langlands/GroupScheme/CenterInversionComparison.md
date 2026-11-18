# Comparing actual normalizer actions on the full centre

These internal derived lemmas compare actual conjugation actions on every test
scheme. The quotient of two normalizing points inducing the same torus action
centralizes that torus and lifts to its supplied actual centralizer. That lift
commutes with the full centre, so the two points have the same centre action.

A point in the range of a torus inverted by an actual normalizer is inverted by
conjugation. Combining these observations transfers inversion to a subgroup's
full centre, assuming that centre maps into the full centralizer centre and that
the latter lies in the containing torus. The centre containment is also shown to
survive arbitrary base change. All statements retain nonreduced test schemes.
No group classification or source-dependent new structural assertion is made.

The entry proposition `Langlands.GroupScheme.FullCenterInversionComparisonStatement` records the precise scope of
`full_center_inversion_of_same_torus_action`: its explicit hypotheses are universally quantified in a
Prop-valued definition. The implemented theorem and proof are retained.
This unit is submitted as a statement because its mathematical entry is
a proposition, rather than a data construction.
