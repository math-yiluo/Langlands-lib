# Open immersion reflection by finite Artinian tests

For a separated algebraic space locally of finite type, a morphism from
a one-point affinoid spectrum to its supplied analytification is represented
by a ring-valued point. Its image fits in one of the Library's affinoid chart
neighborhoods for ring-valued point realization. The affinoid comparison
also gives uniqueness.

A nonempty chart of the analytification of a finite local algebra has that
same coordinate algebra. Precomposing an analytic lift of the corresponding
test with this affinoid chart gives a ring-valued lift by the comparison.
Injectivity of the comparison verifies that its image agrees with the
original test, and the chart algebra equivalence transports the lift back
to the finite local algebra. These are internal deductions from the
affinoid point comparison and the finite local chart equivalence.

For a represented pullback over an affine étale test `Spec A`, take an
affine open `Spec B` of its source with coordinate map `g : A → B`. Let
`m` be a maximal ideal of `B` and let `I` be a positive power of its
contraction to `A`. The quotient of `B` by the extension of `I` has a
maximal ideal and hence an analytic point. Compatibility of the test
maps places the corresponding point of the analytification of `A/I`
in the image of the analytic open immersion. The whole analytic test
lies in this image because its space has one point. The open-domain
lifting property and the one-point comparison give an algebraic lift
of `Spec (A/I)` to the represented pullback.

The pullback projection is a monomorphism. Its injectivity on scheme
points and the uniqueness of the prime of `A/I` place the algebraic
lift inside `Spec B`. The quotient pullback then gives a section of
`Spec (B/IB) → Spec (A/I)`. Passing to algebras gives the injectivity
required by the Artinian open immersion criterion.

For `isOpenImmersion_of_openImmersion`, the analytic open immersion
gives algebraic monicity, which makes the morphism representable under
the stated finite-type and separatedness hypotheses. The Artinian
criterion makes each affine source restriction of a represented étale
test an open immersion. Étaleness is local on the scheme source, so
the entire test projection is étale. Flatness and local finite
presentation of this monomorphism make it an open immersion. Zariski
locality on the affine opens of a target atlas and descent along the
surjective étale atlas give the algebraic-space conclusion.
