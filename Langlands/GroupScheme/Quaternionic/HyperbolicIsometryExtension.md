# Extending isometries along an actual hyperbolic plane

Authors: Worker 124.

This internal development continues the split matrix extension. For the actual
hyperbolic inclusion `E` and polar retraction `R`, put `P = 1 - R E`. The ambient
quotient-valued form is the sum of the pullback of the binary hyperbolic form
along `R` and the pullback of the original form along `P`. This follows from
the Library's hyperbolic quadratic decomposition and vector-value detection.
It supplies an adapted matrix representative of the original form.

The extension `U = R M E + P` satisfies `U R = R M` and `U P = P`. The two
pullback identities therefore show that a binary isometry extends to an
ambient isometry. A parallel rectangular matrix computation over an arbitrary
ring with involution identifies the ambient defect of the adapted
representative with `R` times the binary defect times the conjugate transpose
of `R`. Thus an alternating binary defect gives an alternating ambient defect,
including over rings with nilpotents.

These are derived matrix and quotient-form calculations using the published
hyperbolic decomposition and quadratic pullback APIs. No external-source
correspondence is claimed. The group-scheme morphism and the comparison to an
arbitrary supplied spin cover remain further work.
