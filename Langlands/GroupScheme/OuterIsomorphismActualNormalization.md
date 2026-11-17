# Actual-isomorphism normalization and outer quotients

This internal derived module connects normalization of actual group-scheme
isomorphisms after arbitrary base change to normalization of points of a supplied
isomorphism scheme. Every relative scheme test and every refinement is included.

The classification equivalence recovers an actual isomorphism from each point.
The generic local-isomorphism compatibility lemmas show that refinement is
actual pullback with the specified equal base maps, and the canonical action is
actual inverse precomposition by the evaluated pulled-back action.

`ActualNormalization` retains naturality, invariance under fppf-local inner
equivalence and preservation of the inner class as explicit inputs. The
normalization of a point classifies its normalized actual isomorphism.
Naturality follows through the classification equivalence. For a supplied
relative full-centre adjoint quotient, the evaluated adjoint action is fppf
locally inner, so action orbits have the same normalization.

The unique adjoint section representing the discrepancy between an isomorphism
and its normalization supplies the unique acting point on the original test.
Its inverse is used because the canonical action uses inverse precomposition.
Thus `pointNormalization` supplies the hypotheses of the equalizer construction.
No normalization data are constructed here, and the final reductive existence
theorem remains open.
