# Factoring actual formal homomorphisms through fppf covers

This internal construction, implemented by Worker 921, factors a
formal O-module map h through an actual formal O-module map f when
f has affine fppf local lifting and every actual point killed by f
is killed by h. The rings and finite coordinate types retain the
existing generality, with test algebras in the universe of the base.

The cancellation theorem
`IsFppfLocallySurjective.comp_right_cancel` first shows that f is an
epimorphism of actual formal-module maps. Lift each target point
along a faithfully flat, finitely presented cover, compare the two
composites on that lift, and descend equality using injectivity of
faithfully flat restriction.

`IsFactorValue` says that a prospective value at a target point has
the prescribed h-image on every lift of that point after every
coefficient-algebra map. The kernel inclusion ensures that any two
lifts with the same f-image have the same h-image, by applying the
inclusion to their difference.

Choose one fppf lift and descend its h-image to obtain a factor
value. A common tensor pushout with any other lift proves the
required universal factor-value property. Faithfully flat
injectivity proves uniqueness. The resulting pointwise factor is
natural, additive, and O-linear: these equations are checked on
further faithfully flat lifts and descended.

`Hom.exists_comp_eq` reconstructs the actual formal homomorphism
from that natural O-linear family on points. Extensionality on all
actual points proves its composite with f is h. No factor map is
assumed as part of the input. These are internal factorization
results for the integral scalar-power dual construction required
by `LocalQuasiIsogenyInverseStatement`.
