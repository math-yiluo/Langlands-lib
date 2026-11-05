# Simple-wall factorization from chamber exchange

This derived unit removes the Dynamic ordered-product premise from the
simple-wall inclusion. It works in arbitrary universe `u` over a
nonarchimedean local field, for the actual `P : ParahoricBuildingData G`.
Its structural hypotheses are precisely the apartment axioms,
`RelativeRoot.HasRankOneFactorization P.i`, and the actual supplied
`P.zeroDatum.CoverImageCentralizerNormKernelStatement`.

For a chamber-simple affine root `psi`, an actual relative root `alpha`
with `psi.linear = rootForm P.i alpha`, and a coroot `v` of `psi`, write
`s` for its geometric affine reflection. The theorem
`parahoric_subset_reflection_mul_wall_of_exchange` proves

`P.parahoric C ⊆ P.parahoric (s '' C) · P.apartment.affineRootGroup alpha psi`.

The companion `simpleFactorization_of_exchange` returns, for every
`g ∈ P.parahoric C`, a reflected-parahoric element `b'` and a wall-group
element `u` with `g = b' * u`. This is the exact membership conclusion
of the `AffineIwahoriTitsInputs.simpleFactorization` field. The entry
`chamberSimpleParahoricProductInclusion_of_exchange` retains the same
ambient rational point in the subtype of the displayed product set.
It asserts neither uniqueness of factors nor that the product is a
subgroup. There is no additional premise supplying a point,
cocharacter, decomposition, root enumeration or Dynamic ordered product.

The proof chooses a chamber point and a generic cocharacter positive on
the wall derivative. Actual maximal splitness, reductivity and the
existing roots-and-characters span theorem give the splitness, finite
root set and span hypotheses of the published chamber exchange theorem.
That theorem uses rank-one factorization to write a sharp-fixer element
as a negative generated-root element, a positive generated-root element,
and a rightmost sharp-centralizer element `c`.

The existing
`positiveChamberRootGroups_eq_sharpUnipotentPoints_of_core` identifies
the positive generated subgroup with its actual Dynamic-unipotent
intersection using this surjective core inclusion alone. Since `c`
centralizes the torus and belongs to the point sharp fixer,
`c⁻¹ * p * c` remains in that intersection, hence in the positive
generated subgroup. Thus the rightmost centralizer factor can be moved
to the middle without assuming an ordered-product isomorphism or
injectivity. The actual point-parahoric centralizer comparison, under
rank-one factorization and the retained cover-image hypothesis, puts
`c` in the mapped centralizer-zero subgroup.

Every full-parahoric element is the product of a mapped centralizer-zero
element and a sharp-fixer element. The negative generated-root factor
lies in the reflected sharp fixer by
`negativeChamberRootGroups_le_reflection`. Both centralizer-zero factors
lie in every full parahoric. The positive factor splits into a reflected
sharp-fixer element followed by a wall-group element by
`positiveChamberRootGroups_subset_reflection_mul_wall`. Multiplication
in the reflected parahoric and associativity finish the inclusion.
Reversing its product-set equality gives the membership theorem.

This is a derived composition of existing actual constructions,
chamber exchange, the surjective-core comparison, point centralizer
comparison and the wall-product helpers. No new assertion from an
external source is introduced. The imported earlier factorization
module supplies the negative-wall helper; this proof does not call its
conditional full Iwahori theorem. Rank-one factorization and the actual
cover-image comparison remain hypotheses. The universal
`ChamberSimpleFactorizationStatement` and the unchanged apartment-only
`AffineIwahoriTitsStatement` remain unproved.
