# Pulling literal Iwahori decompositions back to a standard Levi

This internal module composes the published closed-subgroup dynamic-factor
lifting theorem with the existing standard/dynamic subgroup comparisons.
It proves an ordered-intersection decomposition implication, not the full
simultaneous-standard-basis inheritance assertion. No new
original-literature statement is introduced.

The group-level definition `orderedIntersectionComapMap` sends the three
literal intersections for pulled-back subgroups along a homomorphism
`f : H -> G` to the original intersections. It uses precisely the original
ordered multiplication, with the opposite radical first, the Levi second
and the radical third.

`HasIwahoriIntersectionDecomposition.comap_of_factorLifts` assumes that `f`
is injective, that the original `K` has the ordered bijective decomposition,
and that every factor of any original three-factor decomposition of an image
point has a preimage in `H`. It proves the decomposition for the exact
preimages of `K`, the Levi and both radicals. Injectivity follows by mapping
both triples to the original decomposition. For surjectivity, decompose the
image of an original `H`-point, lift each factor, and use injectivity to
recover the original product equality. No topology or representation theory
is needed for this generic implication.

The actual-point theorem
`hasIwahoriIntersectionDecomposition_leviScheme` takes a connected reductive
group, a maximal split torus, a generic cocharacter, an outer root set `J`
contained in the simple roots and an inner set `R` contained in `J`. If the
original subgroup `K` has the standard Iwahori intersection decomposition
for `R` in the ambient group, the theorem proves it for the same `R` in
`Standard.leviScheme i nu J`, at the exact inherited subgroup
`leviSchemeCompact K i nu J`.

The implementation chooses an ambient standard cocharacter for `R` and
proves that it is standard for the intrinsic Levi as well. The latter's
simple roots are exactly `J`, by `simpleRelativeRoots_leviScheme`. Both
standard Levis, radicals and opposite radicals are identified with the
corresponding dynamic subgroups. The published dynamic comap theorems and
`Standard.leviTorusHom_comp` identify all three intrinsic factors with their
exact preimages under the actual Levi embedding.

The factor-lifting hypothesis of the generic implication is supplied by
`Dynamic.exists_triple_factors_of_isClosedSubgroup`: a closed subgroup
containing the defining cocharacter contains all three factors of a
triple-cell decomposition of one of its points. Here the cocharacter factors
through the intrinsic torus. The proof uses the actual lift and exact point
map equations; it imposes no separate radical-product decomposition or
membership assumption on the original factors.

The actual theorem retains the original `K`, cocharacter and selected root
sets. Its algebraic argument has no local-field valuation or characteristic
restriction. The topological-field parameter remains in the existing compact
preimage definition, but no openness or compactness hypothesis on `K` is
needed for this implication.

Compatible split components, chamber contraction and cofinality, inherited
compact-open neighborhood bases and the final simultaneous basis property
are not conclusions of this module. Neither are analytic coefficient or
wave-packet estimates.
