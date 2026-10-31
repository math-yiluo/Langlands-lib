# Relative cohomology and scheme isomorphisms

This internal derived helper packages the published actual pushforward comparison,
closed-immersion higher-direct-image vanishing, and injective acyclicity theorems.
It introduces no geometric base-change or perfectness hypothesis.

For a scheme isomorphism `e : X ≅ Y`, `pushforwardEquivalence e` has functor
`Scheme.Modules.pushforward e.hom` and inverse `Scheme.Modules.pushforward e.inv`.
The composition, equality, and identity isomorphisms for pushforward give the two
inverse identifications; `Equivalence.mk` supplies the triangle identity.

For `R : CommRingCat`, `g : Y ⟶ Spec R`, an actual module `M : Y.Modules`, and
`n : ℕ`, `DerivedSections.relativeCohomologyPullbackIso e g M n` identifies
`Hⁿ_R(X, e^*M)` with `Hⁿ_R(Y, M)`, with the source structure morphism `e.hom ≫ g`.
All schemes and rings have arbitrary common universe `u`, and degree zero is
included. An isomorphism is a closed immersion, so every positive higher direct
image of `e^*M` vanishes. The published pushforward comparison is invertible by
the published injective-acyclicity theorem. Pushforward is an equivalence, hence
the pullback–pushforward adjunction unit `M → e_*e^*M` is invertible. Applying
relative cohomology to its inverse finishes the displayed identification.

The result does not detect vanishing from fibres or prove proper base change.
Its provenance is the internal categorical derivation just described, rather
than a transcription of a separate literature statement.
