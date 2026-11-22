# Compact admissibility and quotients

A surjective intertwining map of compact group representations carries
admissibility to the target when all source vectors are compact-finite and
the source coefficients against linear functionals are continuous. The
Library theorem `KFiniteDual.isSemisimpleModule` makes the source semisimple
over the complex group algebra. Each intertwiner into the target from a
continuous finite-dimensional matrix representation then lifts over that
algebra by `IsSemisimpleModule.lifting_property`. Postcomposition on the
spaces of intertwiners is therefore a surjective linear map from a
finite-dimensional space.

The real and complex compatibility lemmas also take a surjective
intertwiner for the Lie actions. Each target vector is the image of a
compact-finite vector. Precomposition pulls any target functional back to
the source for continuity and differentiation along compact curves.
Applying the intertwiner to the source covariance identity gives the
target identity.

These are consequences of the Library predicates based on J. Getz and
H. Hahn, *An Introduction to Automorphic Representations* (2024),
Definitions 4.4.4 and 4.4.6, printed p. 115 (PDF 130), and the
admissibility condition on printed p. 116 (PDF 131). The Lean proof uses
compact semisimplicity to verify admissibility for the algebraic compact
action on the quotient.
