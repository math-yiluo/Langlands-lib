# Positive roots and the dimension of an actual opposite dynamic quotient

This internal assembly proves the cell and tangent comparison needed by the
positive-root uniqueness argument. It works over every field `k : Type u`,
in every characteristic, for every smooth affine group scheme `G`. No
connectedness, reductivity, maximality or rank assumption is needed. It
assumes a supplied actual quotient with exact fibers on every test scheme;
it neither constructs that quotient nor proves a bound on its dimension.

`Dynamic.oppositeQuotientCellMorphism` is the canonical inclusion of the
affine representative of `U(χ⁻¹)` into `G`, followed by the supplied map
`q : G.X ⟶ Q`. Its definition needs only affineness of `G.X.left`; the
smoothness and quotient hypotheses enter the comparison theorem.

`Dynamic.finrank_tangentSubmodule_opposite_unipotent_cast_le` starts with a
cocharacter `χ` and a morphism `q : G.X ⟶ Q` that is flat, surjective and
quasi-compact. The fiber condition is
`g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ Dynamic.parabolic χ`, for every test scheme and
every pair of its group-valued points. Thus the quotient uses right cosets.
The conclusion bounds the dimension of the intrinsic tangent submodule of
`U(χ⁻¹)` by `topologicalKrullDim Q.left`, with the finite tangent dimension
cast into `WithBot ℕ∞`.

The proof uses the published canonical affine representative of `U(χ⁻¹)`.
Its inclusion is a closed immersion, so the representative is affine.
Published `dynamicSmooth` makes it smooth. The published opposite-cell
theorem and fpqc descent in `Dynamic.OppositeCell.isOpenImmersion_cell`
give an open immersion of this representative into the same supplied `Q`.
The tangent comparison from `Lie.SubgroupCellDimension` identifies its Lie
module with the intrinsic tangent submodule, bounds its dimension by the
dimension of the representative, and then uses monotonicity along the
open immersion.

`RelativeRoot.finrank_tangentSubmodule_unipotent_cast_le_oppositeQuotient`
specializes this comparison to `χ = (-ν) ≫ i` for a homomorphism from a
commutative group scheme `T`. The private sign calculation uses
`Gm.powerHom (-1)` and the additive cocharacter lattice to identify the
opposite of `(-ν) ≫ i` with `ν ≫ i`. Hence the quotient by `P(-ν)` bounds
the actual tangent submodule of `U(ν)`. Splitness of `T` is not needed for
this comparison.

With `T` split,
`two_le_dimension_oppositeQuotient_of_distinct_positive_roots` combines
this bound with the published fact that two distinct positive actual roots
give two disjoint nonzero tangent weight spaces. Every supplied exact
opposite quotient then has dimension at least two.
`positive_roots_eq_of_oppositeQuotient_dimension_le_one` instead assumes
that the same quotient has dimension at most one and deduces that two
positive actual roots are equal. The dimension inequality is explicit and
is not proved here. Both conclusions allow the zero cocharacter and empty
root sets.

The provenance is an internal composition of published opposite-cell,
dynamic representability, smoothness, tangent and dimension results. The
opposite-cell theorem's original source and implemented general-linear
proof are documented in `Absolute.OppositeCellProof`; this unit introduces
no additional external structural assertion. It does not prove properness,
a projective fixed-point bound, maximal-torus conjugacy, maximality
preservation under base change or the exact rank-one parent target.
The four theorem families excluded by the parent task are not used as
premises or proof dependencies.
