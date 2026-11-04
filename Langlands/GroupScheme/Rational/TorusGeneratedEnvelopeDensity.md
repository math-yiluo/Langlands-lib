# Rational density from finite Galois torus splitting

Worker 1436. This internal bridge derives rational density of the fixed torus
envelope from the explicit proposition `TorusFiniteGaloisSplittingStatement`.
Every field has arbitrary universe `u`; density uses an infinite ground field.
There is no assumption of perfectness, reductivity or characteristic zero.

`IsTorus.hasDenseRationalPoints_of_finiteGaloisSplitting` applies the supplied
splitting proposition to an actual torus. Its witnesses are a field extension
in the same universe, its algebra structure, finite dimensionality, the Galois
property and splitting after the actual base change. The published theorem
`TorusDensity.dense_rationalPoints_of_isSplitTorus_baseChange` then gives
Zariski density of the union of images of actual rational points. No splitting
witness is extracted from the existential definition of `IsTorus` alone.

`HasPointedTorusDomination.hasDenseRationalPoints_of_finiteGaloisSplitting`
uses the actual dominant morphism from a torus supplied by pointed domination.
Density passes along it by
`PointTopology.hasDenseRationalPoints_of_denseRange`. This step needs neither
the pointing equation nor a group-homomorphism property of that morphism.

`TorusGeneratedEnvelope.hasDenseRationalPoints_of_finiteGaloisSplitting`
applies that result to the published `D.hasPointedTorusDomination`. It works
for every actual representative of the fixed all-ground-field-tori envelope
in a smooth affine group; connectedness of the ambient group is unnecessary
for this implication. The theorem
`torusGeneratedEnvelopeRationalDensity_of_finiteGaloisSplitting` specializes
it to the exact published `TorusGeneratedEnvelopeRationalDensityStatement`,
whose ambient group is also connected.

`D.rationalPointMeetingOpenOfFiniteGaloisSplitting` constructs an actual
rational point of the envelope whose image meets a supplied nonempty Zariski
open. The returned subtype includes an actual point of `Spec k` witnessing
membership in the open. The construction uses the proved density and the
characterization of density by intersection with nonempty opens; its chosen
rational point is not an additional existence premise.

The provenance is internal: the new assertions compose the published finite
Galois norm-density theorem, dominant-image density, and the fixed-envelope
pointed torus domination theorem. The finite Galois torus-splitting proposition
is an explicit input throughout and is not proved in this module. This unit
therefore does not establish unconditional envelope density or the all-field
pseudo-parabolic rational-lifting theorem. It adds no such input to either
unchanged published target.
