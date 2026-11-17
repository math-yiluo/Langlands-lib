# The actual norm-one splitting on affine coefficient points

This internal derived comparison identifies the published actual scheme splitting
with the original algebra splitting chart over the splitting field itself.
`basePoint_algebraMap` identifies the coefficient scalar map with the inverse of
`Γ(Spec L) ≅ L`. `splittingMap_affine` proves compatibility with the affine section
isomorphism by tensor induction. `splittingIso_affine_points` combines it with the
published all-test splitting formula and the corepresented affine point comparison.

All algebras are finite-dimensional central simple rings over the base field;
there is no division assumption, characteristic restriction or restriction on
the reduced degree. This file is an internal adapter, with provenance in the
existing splitting and affine comparison constructions. It does not itself
classify automorphisms or perform Galois descent.

`affineSplittingEquiv` packages this comparison as a multiplicative equivalence.
`splitAutomorphism` transports an actual norm-one automorphism through the
splitting isomorphism. The general point-conjugation and inverse pullback
comparison lemmas prove that its matrix action agrees with the affine action of
the original automorphism. Full-centre fixation reflection and invariance under
actual isomorphisms preserve the centre-moving premise.

`exists_coefficient_outer_matrix` applies the split outer-matrix construction at
the positive reduced degree. At the identity splitting-field test it substitutes
the affine splitting formula and uses injectivity of the canonical map to global
sections to recover the inverse-transpose formula over the splitting field
itself. Its coefficient automorphism is exactly
`CentralSimpleUnits.coefficientAutomorphism`. This is the formula required by the
separate algebra descent construction; it assumes neither a supplied compatible
torus nor a division-ring presentation.
