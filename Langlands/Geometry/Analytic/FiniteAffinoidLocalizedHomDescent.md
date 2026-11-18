# Localized Hom descent for a finite flat affinoid cover

Author: Worker 790.

`faithfullyFlat_of_flat_of_spectrum_surjective` considers a bounded map
of presented affinoid algebras `A → B` that is flat and surjective on
bounded spectra. For each proper ideal of `A`, the published spectrum
criterion gives an annihilating point. Lift this point to the spectrum
of `B`. Its proper kernel contains the extended ideal, so every proper
ideal of `A` extends to a proper ideal of `B`. The faithful flatness
criterion applies.

`FiniteAffinoidLocalizedHomDescentStatement` adds finite Banach finiteness
and considers a full localized morphism from the small spectrum of `B`
to that of a presented affinoid algebra `C`. If its composites along the
two actual projections of the self-pullback of `B` over `A` agree, it
factors uniquely through the localized spectrum map from `B` to `A`.
The field is complete, ultrametric and nontrivially normed. The field
universe and the prescribed small spectrum universe are independent.

`finiteAffinoidLocalizedHomDescent` converts the localized morphism to a
bounded map `C → B`. Compatibility of `localizedMapEquiv` with
composition translates the two given composites into equality of the
two bounded maps to the completed self-pushout. The bounded descent
theorem supplies a unique lift `C → A`. The same equivalence and
composition law transport the lift, its equation and its uniqueness to
the full localized category. The two projections form a categorical
pullback by the existing small affinoid pushout comparison.

## Provenance

This internal descent step uses the proved detection of proper ideals
by bounded spectrum points, finite Banach pushouts, the small affinoid
Hom equivalence and bounded coefficient descent. Its base, cover and
target are single presented affinoid spectra. Descent on arbitrary
localized étale covering families still requires geometric localization
and gluing.
