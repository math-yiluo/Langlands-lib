# Spanning by real-place standard-module maps

This internal helper for the real-place Rankin–Selberg model bridge is in namespace
`Langlands.Automorphic.OperatorRealization`. It adapts the
complex-place isotypy proof (`ComplexPlaceIsotypic`) and uses the real standard-module
nontriviality proof (`RealStandardNontrivialProof`). It is an algebraic result about the existing operator
realizations and real standard modules.

For an operator realization `S` of `GL_n` over a number field, a real place `w`,
and a list `ds` of real parameter blocks, `IsRealPlaceMap S w ds A` specifies a
complex-linear map from `realStandardKFinite n ds` to `S.Space` that preserves
compact translations and real-direction Lie derivatives at `w`. The definition
retains the membership proofs for the translates and derivatives in the standard
module. These are exactly the two equivariance clauses of
`HasRealPlaceParameter`, without its injectivity and total-rank condition.

`realPlaceIsotypic S w ds` is the supremum of the ranges of all such maps. The
main proved property, `realPlaceIsotypic_eq_top`, says that this subspace is the
whole space when `S` is irreducible for its full operator algebra and has real
place parameter `ds` at `w`.

The proof first shows that composing a place map with an endomorphism commuting
with both place actions gives another place map. Compact translations preserve
each map's image directly. Tensor induction extends real-direction Lie
equivariance to the complexified Lie algebra and shows that it also preserves
each image. Consequently the supremum satisfies
`IsRealPlaceCommutantStable`, and the preceding module makes it either zero or
the whole space.

It cannot be zero: the parameter supplies an injective place map, while its
total-rank condition supplies the hypothesis of
`Archimedean.realStandardNontrivial`. The image of a nonzero source vector is
therefore a nonzero vector in the supremum.

The proof uses irreducibility of the global operator realization. It requires no
irreducibility of the real standard module. It proves no smoothness or growth
bound for a Whittaker coefficient, no comparison with a continuous globalization,
and no Rankin–Selberg functional equation.
