# Homomorphism descent through an fppf group-scheme quotient

This module supports the existence and uniqueness theorem for the derived group
of a reductive group scheme over a base.

This module constructs descent of an actual group-scheme homomorphism through
an fppf homomorphism over any scheme. For `q : H ⟶ Q` flat, surjective and
locally of finite presentation, and `f : H ⟶ G` with
`kernelι q ≫ f = 0`, it constructs `FppfHomDescent.hom q f hk : Q ⟶ G`.
The theorem `FppfHomDescent.existsUnique_hom` states that exactly one
homomorphism `d : Q ⟶ G` satisfies `q ≫ d = f`.

There is no quasi-compactness, affineness, smoothness, separatedness,
commutativity or field assumption on any of the three group schemes.
All objects and the base are in the same arbitrary universe.

This is an internal extension of the published construction in
[`HomDescent`](HomDescent.md). It reuses that module's
`FpqcHomDescent.scheme_comp_eq_of_quotient_eq`, whose proof that `f`
coequalizes equal quotient images needs only the scheme-kernel equation.
Mathlib's `AlgebraicGeometry.Sites.Fpqc` proves that a flat surjective
morphism locally of finite presentation is an effective epimorphism.
Applying its descent construction gives `schemeHom`; canceling the
epimorphism shows that this morphism respects the base map and gives
`overHom`.

The product of `q` with itself over the base is again flat, surjective
and locally of finite presentation, by stability under pullback and
composition. `epi_tensorHom` records that its underlying map in the
slice category is an epimorphism. The unit law follows by precomposition
with the source unit; the multiplication law follows by canceling that
product epimorphism. These laws bundle the descended map as an actual
group-scheme homomorphism. The factor equation is effective-epimorphism
descent's factor equation, and uniqueness follows by canceling `q`.

This construction supplies only descent of a homomorphism that already kills
the scheme kernel. It does not construct a derived group or establish that
an arbitrary homomorphism to a commutative group kills that kernel.
