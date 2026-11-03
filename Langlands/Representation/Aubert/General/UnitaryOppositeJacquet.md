# Opposite Jacquet nonvanishing for admissible unitary representations

This is an internal deduction for the actual normalized Jacquet functors of
a locally compact nonarchimedean group. The group and representation carrier
universes are independent. The two closed radicals `U` and `O` have the same
normalizing subgroup `M`. The structural inputs are one element `g`
centralizing `M`, a cofinal opposite Iwahori contraction basis for this same
element and its inverse, and reciprocity of the actual full Haar modulus
characters on `M`. These inputs are retained; the pair does not construct
them for arbitrary rational points of a reductive group.

`Jacquet.compactOpenCofinal_of_oppositeIwahoriContractionBasis` extracts
compact-open cofinality from the supplied basis, by applying it to each
open subgroup. `Jacquet.HasOppositeIwahoriContractionBasis.symm` exchanges
the radicals and replaces the contracting element by its inverse.

For an admissible smooth object `A` with a chosen invariant positive form
`b`, `unitaryOppositeJacquetDualConjugateEquiv` constructs an actual
conjugate-linear equivalence from `r_U(A)` to the smooth contragredient of
`r_O(A)`. It composes the published Hermitian same-subgroup equivalence
`unitaryJacquetConjugateEquiv` with the isomorphism in
`naturalNormalizedJacquetDualityOfIwahoriContractionsOfReciprocalModulus`.
The first map is induced by `v` mapping to the smooth functional
`w` mapping to `b(v,w)`. The second map is the actual opposite normalized
Jacquet duality obtained from stable evaluation pairings and the retained
contraction and modulus data. No duality isomorphism is supplied as an
extra premise.

`unitary_jacquet_subsingleton_of_opposite` uses this equivalence to show
that vanishing of `r_O(A)` forces vanishing of `r_U(A)` when `A` is
unitarizable. A functional on a zero vector space is zero, so the target
of the constructed equivalence is a singleton. Injectivity gives the
claim. No separation theorem for smooth functionals and no admissibility
of either Jacquet module is needed for this step.
`unitary_jacquet_subsingleton_iff_opposite` reverses the structural inputs
to get the converse. Finally
`not_isUnitarizable_of_jacquet_asymmetry` gives the contradiction used
when `r_U(A)` is nonzero and `r_O(A)` is zero.

The actual declaration dependencies are the two named constructions,
their compact-open Hermitian duality and stable-pairing proofs, and
elementary injectivity and zero-space duality. No new external literature
assertion is introduced. The deduction uses no classification, character
independence, geometric lemma, adjointness or cuspidal-support theorem.
It assumes neither irreducibility nor finite length. It does not prove
the support asymmetry or unitarizability of a particular subrepresentation,
the square-integrability criterion, the rational structural inputs, or
`RationalRankOneSelfAssociationStatement`.
