# Rational sections under an isomorphism of base schemes

This internal prerequisite for Kaletha–Prasad Axiom 4.1.17 (compatibility with
isomorphisms) compares the Library's two actual
section-extension maps. It follows from the pullback universal property and the
existing point functor, without an additional group-scheme hypothesis.

`baseChangeSectionHom_bijective_of_isIso` uses the isomorphism from the base
map, viewed as an object over the original base, to the identity object.
Applying the point functor gives a multiplicative equivalence; composing with
`baseChangeBasePointsEquiv.symm` is exactly `baseChangeSectionHom`.

`GaloisPointComparison.rationalExtend_hom_eq_baseChangeSectionHom` compares both
pullback projections. Consequently, `rationalExtend_bijective_of_bijective`
proves bijectivity whenever the algebra map of fields is bijective, including
the algebra structure induced by a ring equivalence.
