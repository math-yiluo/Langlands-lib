# Pointwise lifting in the analytic étale site

`Langlands.Analytic.SaturatedAtlasPresentation.etalePointwiseLifting` proves
`EtalePointwiseLiftingStatement.{u, v} K` for every complete ultrametric normed
field `K` in universe `u`, with space and atlas index universe `v` independent
of `u`. It applies to every localized analytic base and every cospan in its
étale site.

`finiteAffinoidAlgebraDescent` supplies the descent input of
`finiteOverTargetLocality_of_descent`. The resulting finite target-locality
criterion and `finitePiecesEtaleAllPieces` give localized pullbacks with an
étale base-changed projection by
`localizedEtalePullback_of_targetLocality_and_finitePieces`.

The private cancellation lemma uses those pullbacks to prove étaleness of a
localized arrow `f : A ⟶ B` when `g : B ⟶ X` and `f ≫ g` are étale. Take a
pullback of `f ≫ g` and `g`. Its projection to `B` is étale. Applying the
pullback theorem in the opposite orientation and transporting along the
isomorphism of cones gives étaleness of the projection to `A`. The graph of
`f` is the pullback lift of `𝟙 A` and `f`. It is a section of the projection
to `A`, so `localizedEtaleSectionsOpen` identifies it with an open analytic
domain inclusion up to isomorphism. Such an inclusion is étale by
`etaleOpenDomainStatement`. Composing the graph with the projection to `B`
recovers `f` and proves its étaleness.

`strongEtalePointwiseBaseChange_of_localizedEtalePullback` lifts compatible
ordinary points on strong presentations using the recognized fibre-product
cone. Its localized lifting property transfers that point to a refined strong
square with an étale second leg. `etalePointwiseLifting_of_geometricInputs`
uses right cancellation to recognize the first site arrow as étale and
transports the prescribed points through the quasi-isomorphisms in the two
right fractions. It forms the new object over the base by composing the
étale second leg with the structure map of the second site object. The
full commuting equation of the localized square gives the equation in
`EtaleSite X`, and the two projection equations give the prescribed points.

This is an internal derivation from the named Library constructions. The
pullbacks used in the proof are supplied by the proved analytic criteria,
and the theorem has exactly the field instances of the Library statement.
