# An irreducible external tensor constituent through a nonzero vector

## Statement

Let `G_i`, `i ∈ ι`, be finitely many finite groups and let `σ` be a complex representation of
`∏_i G_i` on a vector space `X` of any dimension, with a nonzero vector `v`.
`FiniteRep.exists_externalRep_intertwining` gives irreducible classes `a_i` of the `G_i` and an
injective linear map from the external tensor product `⊗_i ρ_{a_i}` of the chosen
representatives `ρ_{a_i} = VirtualCharacter.rep (a_i)` to `X` that intertwines the external
tensor action with `σ`.

## Source

This combines two standard facts of the complex representation theory of finite groups: a
nonzero representation of a finite group contains an irreducible subrepresentation (Serre,
*Linear representations of finite groups*, §1.4, Theorem 2), and every irreducible
representation of a product of two finite groups is an external tensor product of irreducible
representations of the factors (Serre, §3.2, Theorem 10), extended by induction to finitely
many factors. In the Library these are `FiniteCharacter.exists_isAtom` and
`FiniteRep.exists_externalRep_equiv`.

## Proof

The span `S` of the orbit of `v` (`FiniteVectors.orbitSubrepresentation`) is a nonzero
finite-dimensional subrepresentation of `σ`, because the group is finite. Transport `S` along
a basis to a representation `τ` on `ℂ^m`, so that the carrier lies in the universe of `FDRep`.
`FiniteCharacter.exists_isAtom` gives an atom `T` of the lattice of subrepresentations of `τ`,
which is irreducible (`FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom`).
`FiniteRep.exists_externalRep_equiv` gives the classes `a_i` and an isomorphism of `T` with
`⊗_i ρ_{a_i}`. The required map is the composite of the inverse of this isomorphism, the
inclusion of `T` in `ℂ^m`, the inverse of the basis transport, and the inclusion of `S` in
`X`; each is injective and equivariant.
