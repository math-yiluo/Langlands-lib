# Automorphisms of finite étale sections at an identity point

This is an internal derived prerequisite for the actual Harris CM level lifts
in `HarrisTaylorCMLevelSurjectivity`. It uses the existing full category
`FiniteEtale.Cover S` of finite étale schemes over `S`, the actual sets
`Fiber s Y = (Over.mk s ⟶ Y.obj)`, and the existing finite-valued functor
`fiberFunctor s hs`. The group `FundamentalGroup s hs` is defined there as
the automorphism group of that functor. Its finiteness parameter
`hs : ∀ Y, Finite (Fiber s Y)` remains explicit.

For any field Ω in the same universe as the schemes, take
`s = 𝟙 (Spec Ω)`. The theorem `fundamentalGroup_identity_eq_one` proves that
every element of this defined group is the identity. The instance
`fundamentalGroup_identity_subsingleton` then identifies any two elements.
Algebraic closure, connectedness, a Galois-category equivalence, and a
comparison with the absolute Galois group are not inputs.

The implemented proof uses naturality on sections. The identity morphism of
`Spec Ω` is finite étale and therefore defines an object `T` of the existing
cover category. Its identity section `e : Fiber s T` is fixed by every
automorphism: its image is still a morphism over `Spec Ω`, and that condition
forces its underlying morphism to be the identity. Each section
`x : Fiber s Y` defines a cover morphism `f : T ⟶ Y` with `e ≫ f.hom = x`.
The existing `smul_naturality` equation therefore gives
`g • x = (g • e) ≫ f.hom = x`. The existing `fundamentalGroup_ext` theorem
concludes `g = 1` from equality of these actions on every section.

At an identity point the functor in this statement is the functor of global
sections of finite étale schemes. Over a field that is not separably closed,
this is not the usual geometric fiber functor used to define its absolute
Galois group. The result makes no assertion that the latter group is trivial.
The intended geometric application uses algebraically closed Ω; the direct
naturality proof establishes the stated result for every field.

The argument is derived from the definitions and naturality laws already in
`FiniteEtale.Definitions` and `FiniteEtale.Pullback`. It is not attributed as
a separate theorem to Harris–Taylor.
