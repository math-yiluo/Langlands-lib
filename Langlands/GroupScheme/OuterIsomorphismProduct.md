# Outer quotients from an equivariant product presentation

This internal construction implements the product-projection step of the
split pinned construction of the outer quotient in Brian Conrad, *Reductive
group schemes* (2014), Theorem 7.1.9(3), pp.245–246. The registered original is
`conrad-2014-reductive-group-schemes`. The module assumes the product
presentation; it does not establish the pinned automorphism decomposition.

Let `I` represent the isomorphisms between supplied group schemes `G,H` over
an arbitrary scheme `S`, and let `a` be an automorphic action of a supplied
group scheme `A` on `G`. Suppose an actual relative scheme `Q` and an actual
isomorphism `e : A.X ⊗ Q ≅ I.parameter` are supplied. The equivariance
hypothesis says that the canonical inverse-precomposition action on
isomorphisms becomes left multiplication in the first factor, on every
relative scheme test. Assume the structure map of `A` is flat and
quasi-compact.

`GroupIsomorphismScheme.outerOfProduct` constructs an
`OuterIsomorphismScheme I a` with class scheme `Q` and class morphism
`e.inv ≫ snd A.X Q`. Flatness and quasi-compactness follow by base change
from `A` and composition with the isomorphism. The product projection has a
section given by the identity point of `A`, so it is surjective.

For a test scheme `T`, write `x(p)` for the first coordinate of `p`. Equal
classes have the same second coordinate, and the unique difference taking
`p` to `q` is `x(q) * x(p)⁻¹`. The Lean proof uses the supplied equivariance,
reconstruction from product coordinates, and cancellation in the group of
`T`-points. Thus all the orbit and uniqueness assertions hold on the
original test, including nonreduced tests. No lift of an `A`-point to `G` is
used. No finiteness or quasi-compactness assumption on `Q` is made.

The definitions of the class map and group coordinate, together with their
reconstruction, invariance, action and unique-difference lemmas, expose the
implemented formulas. The result remains conditional on an actual product
presentation and does not prove outer quotient existence for general
reductive group schemes.
