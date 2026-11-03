# Lifting compatible homomorphisms from a semidirect group scheme

`AutomorphicAction.semidirectHomLift` constructs an actual group-scheme
homomorphism from the already published semidirect group scheme. Its inputs
are an automorphic action of `H` on `N`, homomorphisms `i : N ⟶ G` and
`j : H ⟶ G`, and the compatibility identity on every relative test:
the image of the action is conjugation by the image of the acting point.
The construction is over an arbitrary base scheme and in arbitrary universe.

The proof first applies Mathlib's `SemidirectProduct.lift` to the groups of
points of every relative test scheme. Composition with a test morphism
preserves multiplication, so these homomorphisms form a natural
transformation. Full faithfulness of group-valued Yoneda then yields the
group-scheme homomorphism. The point formula and the underlying scheme
morphism formula identify it with ordered multiplication. Composing with
either canonical factor inclusion recovers its supplied factor map.

`SubgroupFunctor.normalizedProductHom` specializes this construction to the
published normalized-conjugation action. It assumes that the first factor
map is monic and that its range is normalized by the range of the second
factor. Its underlying scheme is `H.X × N.X` and its underlying map sends
the two universal points to the product of their images in that order.
Neither closedness nor an image representative is asserted here.

This is a derived construction from the published automorphic-action and
normalized-subgroup interfaces and Mathlib's semidirect-product universal
property. It supplies the homomorphism used in Milne, *Algebraic Groups*
(2017), Theorem 5.82, printed pp. 120–121, registered source
`milne-2017-algebraic-groups`.
