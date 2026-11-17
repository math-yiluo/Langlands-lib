# Pullback and action compatibility for actual local isomorphisms

This internal derived module records compatibility between the all-test
`LocalGroupIso` interface and actual isomorphisms after base change. It applies
over arbitrary schemes, to every relative test and refinement.

The inverse of `coverPointsEquiv` is the canonical pullback lift of the original
group point and the supplied cover point. Its two projections establish this
description. Evaluation of the actual pulled-back homomorphism then proves
`ofBaseChangeIso_refine`: refining the local family agrees with actual pullback
of the isomorphism. The published direct/iterated and equal-base-map comparison
isomorphisms are retained explicitly in `Descent.pullIso`. Applying the inverse
classification gives `toBaseChangeIso_refine`.

A section of a pulled-back acting group projects to the original acting point
on every relative test. Combining this identity with the definition of the
pulled-back action and the characterization of `toBaseChangeIso` proves
`toBaseChangeIso_twist`: twisting a local family by an acting point is
precomposition of the recovered isomorphism by the actual automorphism of
the pulled-back group.

These results use pullback universal properties and the existing natural
point equivalences. No representability, reductivity, flatness, or local
innerness hypothesis is needed. They supply coherence for later normalized
outer-quotient constructions and assert no existence of pinning data.
