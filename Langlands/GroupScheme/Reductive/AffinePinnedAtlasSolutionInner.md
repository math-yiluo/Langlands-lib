# Inner discrepancy of actual pinned atlas solutions

This internal construction takes a supplied natural pinned comparison `P` and any actual solution `s` of its corrected atlas descent datum. It constructs `solutionLocalIso`, the natural local group isomorphism from the original group to the solution over the actual étale atlas. Its direction is the inverse of the solution's pullback identification.

The proof first identifies the pullback of a canonical overlap with the two direct-pullback comparisons. Equality of the morphisms is checked on their original-group and base coordinates. Pulling the solution's compatibility equation to a common test of two atlas coordinates then gives `L_a ≪≫ transition_ab = L_b`, where `L_a` is the direct pullback of the solution identification. Cancelling the comparisons proves this equality for the actual group-scheme isomorphisms.

The discrepancy of `solutionLocalIso` is therefore the inverse corrected atlas transition. The existing quotient point `transitionInnerPoint` induces exactly that inverse transition. For any supplied full-centre fppf quotient and action restricting to conjugation, `solutionLocalIso_hasInnerDiscrepancy` proves the all-refinement inner-discrepancy condition by equality of the actual relative automorphisms.

These are derived consequences of the Library's actual descent and local-isomorphism interfaces. No new literature assertion is made. The comparison and actual solution remain supplied hypotheses; this module does not assert their existence or the final unconditional quasi-split inner-form theorem.
