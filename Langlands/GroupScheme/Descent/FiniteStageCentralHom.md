# Centrality at finite fields of definition

This internal construction builds on the published finite fields of
definition for actual group-scheme homomorphisms.

`Descent.FiniteStage.HomModel.isCentral` reflects centrality from the
original homomorphism to its model. Its exact recovery equation expresses
the base change of the model as the original homomorphism transported by
the tower comparison isomorphisms. Centrality survives those
isomorphisms and then descends by flat surjective base change.

`Descent.FiniteStage.centralClosedHomModel` chooses a finite model for a
central closed homomorphism over an algebraic field extension, retaining
closedness, centrality, and the exact recovery equation. Its source is
quasi-compact and quasi-separated, its target locally finitely presented,
and both are affine schemes over the ground field. This construction
does not assume any woundness criterion.
