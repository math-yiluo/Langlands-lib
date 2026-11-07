# Raising the factor universe of a cuspidal spectral presentation

This is internal infrastructure derived from the Library's actual representation
and restricted tensor constructions. It does not assert a new literature result
or existence of a spectral presentation.

Given `P : CuspidalSpectralPresentation.{uF, uV} S`,
`CuspidalSpectralPresentation.universeLift.{uX}` gives a presentation of the same
cuspidal realization with factor carriers in universe `max uV uX`. In particular,
a presentation with factor universe zero can be raised to any requested universe.
The finite slice, both exceptional sets and all numerical spectra are retained.

Each local factor is replaced by its existing `SmoothRep.universeLift`, with
the action transported by `ULift.up` and `ULift.down`. The references are lifted
by `up`. `RestrictedTensor.congr` gives an actual linear equivalence of tensor
products; `FiniteAdelicGL.tensorIntertwiner` verifies equivariance. Composing its
inverse with the original presentation presents the original embedded slice.

The embedded local components use independently chosen complementary vectors,
so equality of these subspaces is not asserted. `universeLiftLocalEquiv` instead
composes their factor equivalences with the inverse of `SmoothRep.universeLiftEquiv`.
Consequently `universeLift_localComponent_isoClass` preserves every local smooth
isomorphism class, and the two following equivalences preserve irreducibility
and admissibility at every finite place. The unramified spectra are transferred
using `LocalRealization.padicClass_eq_iff` and
`LocalRealization.hasSphericalHeckeSpectrumClass_iff`. The resulting
`universeLift_spectralSystem` equality is definitional.

The construction supports the proof task for the exact target
`Langlands.Global.HenniartGlobalizationStatement.{uK, uQ, uW, uP}`: an all-local
irreducible presentation with factor universe zero must be usable at arbitrary
`uP`. This module does not prove that target.
