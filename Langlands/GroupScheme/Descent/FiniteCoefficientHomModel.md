# Simultaneous finite coefficient models of group homomorphisms

Internal construction from the published finite coefficient
source and separated target models. The two explicit proof premises are
`HomGeneralStatement` and the scheme-level `MonomorphismStatement`.

`SimultaneousHomModel` records source and target groups over one finitely generated
coefficient subalgebra, an affine smooth source, a separated finitely
presented target, an actual homomorphism, and group isomorphisms recovering
the supplied groups. Its recovery square identifies the specified
homomorphism, not merely the two groups separately.

`SimultaneousHomModel.enlarge` pulls both groups and the homomorphism to a further
finitely generated coefficient algebra. The natural direct/iterated
pullback comparisons retain the recovery square, and finite generation
is transitive along the coefficient tower.

`exists_homModel` first models the affine smooth source, then models the
separated finitely presented target over its coefficient algebra. It
pulls the source to the target's coefficients and conjugates the supplied
homomorphism by the two recovery isomorphisms. The homomorphism descent
premise supplies the final coefficient stage and the commuting square.
All requested finite coefficients remain in that stage.

For a monic supplied homomorphism, `SimultaneousHomModel.mono_over_algebra` transfers
monicity along the recovery isomorphisms. `SimultaneousHomModel.exists_mono` applies
the explicit scheme monicity descent premise and enlarges the model.
This supplies an actual monic model, but does not assert reductivity of
its source or a closed-immersion conclusion.
