# Full-flag adapted bases and solvability

The namespace `Langlands.LinearAlgebra` constructs an adapted basis and an
injective homomorphism into the group of invertible upper triangular
matrices. It proves solvability for every subgroup of `GL_N(K)` preserving
a full flag. The field `K` is arbitrary, its universe is arbitrary, and
`N` may be any natural number, including zero and one.

The input is a monotone family
`F : Fin (N + 1) → Submodule K (Fin N → K)` with
`Module.finrank K (F j) = j` for every index `j`. For a subgroup
`G : Subgroup (Matrix.GeneralLinearGroup (Fin N) K)`, the preservation
hypothesis requires
`g *ᵥ v ∈ F j` whenever `g ∈ G` and `v ∈ F j`. This is a condition on
the actual matrix action, requiring only inclusion.

## Adapted basis

`fullFlagVector F hF hdim i` chooses a vector in `F i.succ` outside
`F i.castSucc`. Monotonicity and the distinct dimensions of these two
subspaces guarantee that the difference is nonempty. The lemmas
`fullFlagVector_mem` and `fullFlagVector_not_mem` retain these properties.

A private induction proves that such successive-difference vectors are
linearly independent. The initial vectors lie in the penultimate
subspace, while the final vector does not; Mathlib's
`linearIndependent_finSucc'` gives the induction step. There are `N`
vectors in an `N`-dimensional space, so
`basisOfLinearIndependentOfCardEqFinrank'` produces `fullFlagBasis`.
`fullFlagBasis_apply` identifies its vectors with the chosen vectors.

`fullFlagBasis_flag` proves
`(fullFlagBasis F hF hdim).flag j = F j` at every index. The forward
containment follows from monotonicity and membership of the chosen
vectors. A private dimension computation identifies the basis flag
with the span of its first `j` vectors, indexed by `Fin j.val`.
Their linear independence gives dimension `j`, so
`Submodule.eq_of_le_of_finrank_eq` turns the containment into equality.
The same proof covers the empty basis when `N = 0`.

## Coordinate embedding and solvability

`basisCoordinates b` is the multiplicative equivalence from `GL_N(K)`
to itself obtained by passing from matrices to endomorphism units and
then expressing those endomorphisms in the basis `b`. Its entry formula
is proved by `basisCoordinates_apply`:
the entry in row `i`, column `j` is
`b.repr (g *ᵥ b j) i`.

`basisCoordinates_mem_upperTriangular` uses the adapted basis and flag
preservation to show that these entries vanish for `j < i`. Indeed,
`g *ᵥ b j` belongs to `F j.succ = b.flag j.succ`, and
`Module.Basis.mem_flag_iff_repr_eq_zero` says that its coordinate at
`i` vanishes when `j.succ ≤ i.castSucc`.

`fullFlagTriangularEmbedding F hF hdim G hG` restricts this coordinate
equivalence to a monoid homomorphism
`G →* Langlands.GeneralLinear.upperTriangularSubgroup N K`.
Its underlying matrix is recorded by `fullFlagTriangularEmbedding_val`.
`fullFlagTriangularEmbedding_injective` follows from injectivity of the
coordinate equivalence and the subgroup inclusion.

`isSolvable_of_mulVec_mem_fullFlag` transfers the published theorem
`Langlands.GeneralLinear.UpperTriangularSolvable.isSolvable` along this
injective homomorphism, using
`Group.isSolvable_of_isSolvable_injective`.

`isSolvable_of_injective_representation_fullFlag` gives the corresponding
result for a group `H` with an injective representation
`ρ : H →* GL_N(K)` whose matrices preserve the flag. It first applies
the subgroup theorem to `ρ.range`, then transfers solvability to `H`
through `ρ.rangeRestrict`.

## Provenance and scope

This is an internal linear-algebra construction derived from Mathlib's
subspace, basis, matrix-coordinate and solvable-group APIs and the
published upper triangular group construction. No external structural
theorem is assumed. Worker 1399 designed the full-flag preservation
interface for the geometric consumer; Worker 135 implemented the
constructions and proofs.

The result supplies the algebraic solvability step once a preserved full
flag has been obtained. It constructs neither a geometric flag variety
nor a fixed point, and it does not establish the full
`Langlands.GroupScheme.BorelConjugacyStatement`.
