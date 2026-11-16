# Full quasi-isomorphism fractions for localized isomorphisms

Author: Worker 208.

This derived internal unit proves that the actual localization reflects
isomorphisms into full strong quasi-isomorphisms. The field, space and
original chart-index universes `u, v, w` are independent. The field is
complete and ultrametric; no separation hypothesis is imposed.

`isQuasiIso_of_localizedRightFraction_eq_id` starts with an actual right
fraction representing an identity. Exact common refinement compares it
with the identity fraction. The comparison arrow to its source is a
quasi-isomorphism by right cancellation of the denominator. The refined
numerator is the same full quasi-isomorphism as the refined denominator,
so the proved source cancellation shows that the original numerator is
a full quasi-isomorphism.

`isQuasiIso_of_isIso_localizationFunctor_map` takes an actual strong map
whose image is an isomorphism. Choose an actual right fraction for its
inverse. Composing the inverse fraction with the mapped original arrow
gives an identity fraction with numerator `ψ.f ≫ f`, hence this numerator
is a quasi-isomorphism. Composing in the other order using the constructed
Ore fraction gives another identity fraction, whose numerator is
`OreLift ≫ ψ.f`. Two-out-of-six for these two consecutive composites
proves that `f` is a full strong quasi-isomorphism. The argument uses exact
localized equations and complete common refinement, without faithfulness
of the underlying-space functor.

The selected definition `quasiIsoFractionOfIso` chooses the existing
right-fraction representative of a localized isomorphism and proves that
its numerator is also a full quasi-isomorphism. Its mapped numerator is
the composite of the mapped denominator with the original isomorphism,
so reflection applies. The denominator is already a full
quasi-isomorphism by the fraction type. The final theorem proves that
this selected fraction interprets exactly as the original isomorphism.

The definition returns actual fraction data and the proved numerator
condition. It assumes neither a supplied fraction nor a supplied
geometric inverse. Its provenance is the Library's right-fraction
calculus plus the included proved domain cancellation and two-out-of-six
results; no external theorem claim is made.

The same contribution includes `LocalizedEtaleComposition`, whose paired
Markdown explains the application to the existing analytic étale site.
The previous helper pairs are unchanged dependencies included pending
integration.
