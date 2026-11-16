# The local D4 index when a full-star-fixed leaf exists

This internal derived unit applies to a simply connected absolutely
almost-simple group over a nonarchimedean local field, at arbitrary universe
and in every field and residue characteristic, including characteristic two.
It assumes split rank one and an equivalence `e` identifying the actual
Cartan matrix with `CartanMatrix.D 4`.

`localRankOneD4_presentation_and_marking_of_fixed_leaf` assumes that some
actual leaf `a`, characterized by `e a != 1`, is fixed by every automorphism
of the separable closure over the ground field. The leaf need not occupy
any particular place in the original numbering. The theorem proves both
existence of `LocalRankOneTypeDPresentation K G 4` and
`IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1)` for the reoriented
numbering `d4NumberingAt e a`. Thus the entire distinguished set is the
central vertex.

`localRankOneD4PresentationOfFixedLeaf` chooses this proved presentation.
It is an actual central division algebra of ground-field dimension four,
a first-kind involution with symmetric dimension three, a nondegenerate
quotient-valued quadratic form on `Fin 4` of quadratic Witt index one, and
an actual morphism from the supplied group satisfying `IsSpinCover`.
The definition uses `Classical.choice` on the theorem's proved existence;
it introduces no further assumption.

The proof reorients the actual diagram so that the fixed leaf is numbered
`0`. `d4NumberingAt_cartan` preserves every Cartan entry, while
`star_fixes_nonfork_of_D4_fixed_leaf` proves fixation of both numbered
nonfork vertices. Applying
`localRankOneTypeD_presentation_and_marking` then supplies the actual
quaternionic model and the complete marked subset. In particular this
argument uses the previously established local quotient-valued type-D
presentation, including its characteristic-two scope.

`hasRankOneOuterD4Index_of_fixed_leaf` additionally assumes that the full
star action is nontrivial. It proves exactly the published
`HasRankOneOuterD4Index` predicate. After reorientation, the previously
proved `hasRankOneOuterD4Index_of_fixes_nonfork` applies: the full image
consists exactly of identity and the transposition of vertices `2` and `3`,
and the distinguished vertex is exactly `1`.

`localRankOneD4_index_or_transitive_leaf_marking` records a remaining-case
reduction under this same nontriviality assumption. Either the published
outer-D4 predicate holds, or there is no globally fixed leaf and the entire
distinguished subset is exactly the center or exactly the three leaves.
The proof splits on existence of a globally fixed leaf, applies the exact
outer-D4 theorem in the first branch, and applies
`D4_marking_cases_of_no_fixed_leaf` in the other. The accompanying
`TypeD4StarOrbits` module proves transitivity of the full action on leaves
in that second branch.

The existence of a globally fixed leaf is retained as an explicit premise
of the presentation and outer-index theorems. This unit does not establish
that premise for all local D4 groups, exclude trialitarian groups or inner
D4 groups, bound higher type-D ranks, or prove the full
`LocalRankOneTitsIndexStatement`.
