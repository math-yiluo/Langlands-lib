# Smooth invariants as maps from the trivial representation

Author: Worker 280.

This internal helper adapts the published
`Langlands.Cohomology.EquivariantComposite.InvariantsHom` to smooth
representations with independent coefficient and group universes. It uses the
published `smoothTrivialAdjunction` and the `trivialSmoothRep` of the analytic
composite statement. It asserts no new geometric theorem.

For a commutative ring `R : Type uR` and a group `G : Type uG` with a topology,
`trivialHomInvariantsAddEquiv` evaluates equivariant maps from the trivial
representation on `R` at one. It composes the additive adjunction equivalence,
the equivalence between module morphisms and linear maps, and evaluation of a
linear map on the free rank-one module `R`. Naturality is checked on elements.
`invariantsHomIso` packages the inverse equivalences as a natural isomorphism
after forgetting scalar multiplication.

`invariantsHomologyIso` applies this natural isomorphism termwise to complexes
of any shape and takes homology. The exact forgetful functor from modules to
abelian groups commutes with homology by the published
`LeftExactHomology.homologyNatTrans`. No invariants exactness hypothesis is
used. These helpers supply the invariants-to-Hom step in the resolution proof
of Berkovich's composite identification.
