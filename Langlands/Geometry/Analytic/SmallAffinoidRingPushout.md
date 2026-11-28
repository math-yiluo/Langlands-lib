# Localized affinoid pullbacks from finite Banach ring pushouts

Take a pushout square of commutative rings whose four objects are presented
affinoid algebras over a complete ultrametric normed field `K` and whose maps
are bounded `K`-algebra maps. Suppose the first map into the pushout algebra
is finite Banach. For a pair of bounded maps out of the sides of the square
that agree on the base, `ringPushoutLift` constructs the bounded lift from the
pushout algebra. The ring universal property supplies the underlying ring map.
Its equation on the finite leg gives its compatibility with the scalars.
`BoundedAlgHom.ofFiniteBanachTriangle` then gives the bound from the norm
control on coefficient lifts along that leg. The uniqueness is the uniqueness
of the ring lift.

When the four spectra are small in the chosen space universe,
`localized_isPullback_of_ring_isPushout` proves that their spectrum maps form a
pullback in the localized analytic category. The retained greatest charts
identify the ring pushout lift with the bounded lift required by
`TopChartPushout`. The resulting strong pullback supplies lifts with the
identity as source refinement. `IsRefinedStrongPullback.isPullback` extends
this universal property to localized morphisms with arbitrary sources.

The construction is derived from the ring pushout property, the finite Banach
coefficient estimate and the Library's greatest chart and localization
comparisons. The field can have trivial norm and the space universe is
independent of the field universe.
