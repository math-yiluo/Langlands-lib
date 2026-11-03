# Realizing integer quasiinverses by actual torus homomorphisms

Worker 384, with the integral quasiinverse algebra supplied by Worker 1444.
This is an internal supporting construction for the split-torus isogeny proof.
It uses the published actual character lattice equivalence and coordinate
characters and cocharacters, together with the character comparison and finite
cokernel results in `SplitTorusIsogenyCharacters`.

Let `k` be any field and let `I` and `J` be finite coordinate types, all in an
arbitrary common universe. Write `T_I` and `T_J` for the actual standard split
tori in additive notation. For an integer-linear map
`b : (I → ℤ) →ₗ[ℤ] (J → ℤ)`, `fromCharacterColumns I J b` is the actual morphism

`g = ∑ i, (characterLatticeEquiv k J).symm (b (Pi.single i 1)) ≫ single i`.

Its projection onto the `i`th coordinate is exactly the character specified by
`b (Pi.single i 1)`. The proof distributes composition over the finite sum and
uses the published duality `single i ≫ proj j = δᵢⱼ`. Equality of all coordinate
projections determines equality of actual torus homomorphisms.

For an actual torus homomorphism `f : T_I → T_J`, let `F` denote its published
character pullback in integer coordinates. If `F ∘ b = n • id`, then
`comp_fromCharacterColumns` proves `f ≫ g = n • id` on `T_I`. It checks each
projection using the actual character equivalences and the equality obtained
by applying `F ∘ b = n • id` to the corresponding coordinate vector.

If the underlying scheme morphism of `f` is epimorphic, then
`fromCharacterColumns_comp` also proves `g ≫ f = n • id` on `T_J`.
The published `characterMap_injective_of_epi` allows checking each character
identity after pulling back along `f`. Associativity and the first composite
identity then reduce it to bilinearity of composition over integer multiples.
This step does not assume that `f` is surjective on field-valued points.

Finally, `exists_integer_quasiInverse` assumes that the underlying scheme map
of `f` is both finite and epimorphic. The published character results give
injectivity and finite cokernel for `F`. The internal integer-module theorem
`SplitTorusIsogeny.exists_quasiInverse_of_injective_finiteCokernel` supplies a
nonzero integer `n` and a reverse linear map `b` with the required composite
identity. Realizing its columns gives an actual `g : T_J → T_I` with both
composites equal to multiplication by `n`.

The construction also covers empty coordinate types. No characteristic,
separability or perfectness restriction is imposed on `k`. This supporting unit
does not itself assert the cocharacter comparison for arbitrary chosen split
tori; that conclusion still requires transport by splitting isomorphisms and
application of the actual cocharacter maps.
