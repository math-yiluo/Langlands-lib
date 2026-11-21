# Stability of localized analytic étale morphisms

`Langlands.Analytic.SaturatedAtlasPresentation.localizedEtaleStability` proves
`LocalizedEtaleStabilityStatement.{u, v} K` for the actual localized analytic
étale predicate. It applies to complete ultrametric normed fields `K : Type u`
with independent space and chart-index universe `v`. The composition clause
uses the instance from `LocalizedEtaleComposition`.

For right cancellation, let `f : A ⟶ B` and `g : B ⟶ X` be localized maps with
`g` and `f ≫ g` étale. The target-locality criterion from
`finiteOverTargetLocality_of_descent`, applied to the proved
`finiteAffinoidAlgebraDescent`, combines with `finitePiecesEtaleAllPieces` to
give a pullback with étale second projection for any cospan with an étale
first leg.

Apply this construction to `f ≫ g` and `g`. The projection `q : P ⟶ B` is
étale. Applying it in the opposite orientation supplies an étale second
projection there. `etale_snd_of_isPullback` transports that étaleness to the
projection `p : P ⟶ A` of the original pullback. The pullback lift of `𝟙 A`
and `f` gives a graph `s : A ⟶ P` with `s ≫ p = 𝟙 A` and `s ≫ q = f`. The
first equation lets `localizedEtaleSectionsOpen` factor `s` as an isomorphism
followed by an open analytic domain inclusion. The isomorphism is étale and
`etaleOpenDomainStatement` makes the inclusion étale. Composition with `q`
then gives étaleness of `f`.

This is an internal derivation of the stability statement in `GeometricInputs`.
Worker 271 developed the graph argument in the proof of pointwise lifting.
The theorem uses the published analytic criteria to construct the pullbacks
and quantifies over arbitrary localized `f`.
