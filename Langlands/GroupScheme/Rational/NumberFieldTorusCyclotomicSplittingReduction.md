# From Galois cocycles with lattice coefficients to torus cocycles

`numberFieldTorusCocycleCyclotomicSplitting_of_unitsLattice` proves
`NumberFieldTorusCocycleCyclotomicSplittingStatement` assuming
`NumberFieldUnitsLatticeCyclotomicSplittingStatement`. The latter
supplies the arithmetic vanishing from the cyclotomic argument in
Platonov–Rapinchuk, *Algebraic Groups and Number Theory*, §6.5,
Proposition 6.20 and Lemma 6.20 (printed p. 341). The reduction
compares its Galois-cohomological conclusion with the group-scheme
cocycle on a finite Galois cover.

For a torus `T` over `K`, put `Ω = SeparableClosure K`. The finite
Galois splitting theorem gives a splitting of `T` over `Ω`. The
cocharacter lattice `X` over `Ω` is finite free, and its action is
smooth because the group fixing a finite field of definition acts
trivially. `tensorPointIso` gives the equivariant identification
`Ωˣ ⊗ X ≃ T(Ω)`, with the points written additively.

The values of the cover cocycle on `L/K` inflate to `Gal(Ω/K)` by
restriction of automorphisms and extension of points to `Ω`.
The cocycle identity is preserved by equivariance. The restriction
of automorphisms to `L` is locally constant, so the inflated cocycle
is locally constant. A trivialization of the `m`-th power on the
cover yields an additive coboundary for `m • c` after taking the
inverse of the multiplicative witness, in accordance with the two
coboundary conventions.

The lattice statement gives a positive `N` with the required prime
divisors and a point `a ∈ T(Ω)` that trivializes the inflated cocycle
on the subgroup fixing `E₀ = K(ζ₀)`, where `ζ₀` is primitive of
order `N`. The point representation is smooth by the tensor
identification, so a subgroup fixing a finite normal intermediate
field fixes `a`. Take a finite normal extension `M/K` inside `Ω`
containing this field, `E₀` and the image of `L`. The point descends
to `T(M)`. On the finite Galois cover `M/E₀`, the inverse of this
point gives the trivialization, using a lift of each automorphism
to `Ω` to verify the coboundary identity.
`GaloisCocycle.isTrivial_baseChange_of_scalarExtension` then gives
triviality on the pulled-back cover over `E₀`.

Finally, `E₀` is a splitting field of `X^N - 1` over `K`. Every
extension `E/K` containing a primitive root of order `N` splits
that polynomial and admits a `K`-embedding of `E₀`. The factorization
of `Spec E → Spec K` through `Spec E₀` transfers the trivialization
to `E`.
