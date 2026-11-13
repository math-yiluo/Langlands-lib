# O-linear formal homomorphisms

For finite-coordinate formal O-modules `M` and `N` over the same commutative
O-algebra `R`, `ModuleLaw.Hom M N` consists of a homomorphism of the underlying
formal groups commuting with every formal scalar endomorphism. Thus the
commutation identity is an equality of formal power-series maps.
`Hom.onPoints` evaluates it to an O-linear map on each series-point module.
Conversely, `ofPointLinear` recovers formal scalar commutation from O-linearity
on all series points, by evaluating at the tuple of coordinate variables.

The Hom objects form an additive commutative group, with addition and inverse
inherited from formal group Hom. Multiplication by `a : O` postcomposes with
the target endomorphism `[a]`. This defines an O-module, and
`onPointsLinear` is O-linear in the formal homomorphism as well.
Composition is O-bilinear (`compLinear`); the endomorphisms form a ring whose
multiplication is composition. Coefficient extension along an O-algebra
homomorphism preserves O-linear formal homomorphisms and defines the linear
map `mapLinear` between the Hom modules.

`ModuleLaw.Iso` is a pair of inverse O-linear formal homomorphisms.
Evaluation gives an O-linear equivalence of point modules.

This is derived infrastructure for the rational Hom in Drinfeld,
*Coverings of p-adic Symmetric Regions* (1976), §2 A, printed p.109:
quasi-isogenies are invertible elements of `Hom(X,Y) ⊗_O K`.
The preceding definition of a formal O-module is in §1, printed p.108.
The explicit coordinate Hom type, the faithful series-point proof method
and the linear-map packaging are internal implementation choices.
This module constructs integral O-linear Hom; rationalization, heights
and the locally glued formal groups permitted at the end of §1 remain
subsequent work.
