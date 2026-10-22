# Finite injective normalization of strict affinoid quotients

Author: Worker 56.

`PresentedStrictAffinoidAlgebra.NoetherNormalizationStatement K` says that
every nonzero presented strict affinoid algebra over the complete
ultrametric normed field `K` admits a bounded, injective `K`-algebra
homomorphism from a finite-variable strict Tate algebra, and is finite as a
module over its image. The number of source variables is at most the
arity of the given presentation. The quotient, its norm, and the bounded
algebra map are the actual constructions in `Affinoid`.

The source is Proposition 2.4.1, page 6, and Corollary 2.4.2, page 7, of
the retained fourteen-page notes of part of Vladimir Berkovich's course,
“2. Affinoid algebras.” Corollary 2.4.2 gives the bounded finite
monomorphism. The arity bound follows by applying Proposition 2.4.1 to the
surjective presentation map; its construction retains a subset of the
original number of coordinates. The Lean target records this consequence,
without claiming the full ambient chart returned in Proposition 2.4.1.

`Nontrivial A` states that the quotient is nonzero. There is no hypothesis
that `A` is reduced or a domain, and no hypothesis that the valuation of
`K` is nontrivial. Finiteness is `RingHom.Finite`, meaning finite
generation of the target module for the scalar action induced by the
map. The target is a proposition definition; neither a normalization map
nor its finiteness is stored in the input presentation.

Registered source:
`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
PDF SHA256
`c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`,
retained at
`literature/Retained original of Berkovich's Affinoid algebras course notes (14 pages).pdf`.
The note-taker and publication date are unidentified.
