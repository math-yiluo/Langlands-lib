# Uniform bounds for fibres of affine étale morphisms

This derived helper translates the algebra bound from
`EtaleAlgebraUniformPointBound` into a bound on actual scheme-valued points.
It supports the bounded geometric-fibre ingredient in Stacks Lemma 68.8.4,
Tag 07S9. The registered source is `stacks-stratification-2026-11-02`,
`07S9.html`, statement and proof. No stratification or quotient is assumed
or constructed here.

For an étale morphism `f : X ⟶ Y` of affine schemes in universe `u`,
`affineEtalePointBound f` is the algebra bound for the map on their rings of
global sections. Its scalar structure is precisely `f.appTop.hom.toAlgebra`.
Étaleness of this algebra follows from the affine characterization of an
étale scheme morphism.

`affineEtale_fibrePoints_finite_card_le` says that, for every field `K` in
universe `u` and every actual morphism `a : Spec K ⟶ Y`, the type of
morphisms `g : Spec K ⟶ X` satisfying `g ≫ f = a` is finite and has natural
cardinality at most `affineEtalePointBound f`. The bound is independent of
both the field and the base point.

The proof uses the published `FiniteEtale.affinePointEquiv` and its
composition formula. A fibre point gives an algebra homomorphism from
`Γ(X, ⊤)` to `K`, with scalar structure on `K` induced by `a`. This map
is injective by the affine point equivalence. The algebra finiteness and
cardinality theorem therefore gives the result. No algebraic closedness,
Noetherian hypothesis, or separability hypothesis on `K` is needed.
