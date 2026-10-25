# Cyclic subrepresentations and group-algebra presentations

This is an internal algebraic construction used to assemble restricted tensor
factorizations. It reuses the generic orbit subrepresentation from
[`FiniteVectors`](FiniteVectors.md) and adds its monoid-algebra presentation.
It applies in particular to the first restriction of a product representation
used in `Langlands.TwoFactorExistence.spanOrbit`. It does not assert a factorization
or irreducibility theorem and does not require any topological hypotheses.

For a representation `ρ` of a monoid `G` on a vector space `V` over a field `K`,
`Langlands.Cyclic.orbitSpan ρ v` abbreviates the existing
`Langlands.FiniteVectors.orbitSubrepresentation ρ v`: the linear span of the
vectors `ρ g v`, with the restricted action. Its containment and minimality
lemmas reuse the existing proofs. It contains `v` and lies in every
subrepresentation containing `v`. Its carrier is a subspace of `V`, hence has the same universe as `V`,
independently of the universes of `G` and `K`.

`generator` is `v` as an element of that subspace; it is nonzero exactly when
`v` is nonzero. `inclusion` is the intertwining subspace inclusion.
`algebraEvaluation` sends an element `a` of the monoid algebra to
`ρ.asAlgebraHom a v`. Its range is exactly the orbit span: algebra induction
proves one containment, and the singleton monomials prove the reverse.
`presentation` corestricts this evaluation to the orbit span and is surjective.
`map` restricts an intertwiner to the cyclic subrepresentations of a generator
and its image, and sends the distinguished generator to the distinguished
generator.

The definitions and proofs are derived directly from Mathlib's representation,
subrepresentation, linear-span, and monoid-algebra APIs. Their provenance is
internal; they are not claimed as separately numbered results in Flath's
article. No commutativity among distinct actions, absolute irreducibility,
finite-dimensionality, or tensor-product conclusion is assumed or proved here.
