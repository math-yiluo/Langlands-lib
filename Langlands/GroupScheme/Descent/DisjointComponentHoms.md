# Morphisms over arbitrary disjoint scheme components

This internal generalization of `Descent.FiniteComponents` works with an
arbitrary index type in the universe of the schemes. The supplied maps
`p i : Z i ⟶ S` must have an isomorphism as their coproduct map. There is
no finiteness, connectedness, affineness, or nonemptiness hypothesis.

Each component map is the composite of a coproduct inclusion with the
supplied isomorphism, hence is an open immersion. The component images
cover `S` and are pairwise disjoint. Their inverse images along every
scheme over `S` are therefore a disjoint open cover. Mathlib's coproduct
criterion for a disjoint open cover shows that the coproduct of those
actual pullbacks maps isomorphically to that scheme.

`schemeHom` uses this pullback decomposition to assemble the supplied
component morphisms. `overHom` proves that the assembly preserves the base.
The restriction and assembly identities show that component restriction is
fully faithful. Applying that fully faithful cartesian monoidal functor to
group objects gives `groupHom`, with its restriction and uniqueness laws.
`groupIso` assembles supplied component isomorphisms by assembling their
forward and inverse homomorphisms. The component identities prove the two
inverse laws. The pointwise group-scheme restriction is fully faithful too.

The implementation follows the existing finite-component construction;
its new geometric step proves stability of arbitrary small coproduct
decompositions under pullback directly from disjoint open immersions. This
is an assembly construction on supplied decompositions, without an object
descent or quasi-split existence assertion.
