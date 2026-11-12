# Simultaneous minima along a rational subgroup chain

Author: Worker 83.

This derived module extends the published one-representation orbit-height minimum
to a finite descending chain. Each step has its own actual algebraic representation,
nonzero rational vector and rational subgroup. Later subgroups must act by nonzero
rational scalars on earlier vectors. The resulting minimum inequalities all hold at
one rational translate. This supplies no root estimate or chamber bound.

## Data and conclusion

Let `F : Type u` be a number field and `G` an actual group scheme over `F`.
For each natural index `i`, choose a dimension `d i`, an actual
`MatrixRepresentation G (Fin (d i))`, a vector `v i`, and a subgroup
`Q i` of `RationalGroupPoints F G`. The theorem uses only indices below a
finite length `r`, where the vectors must be nonzero. The subgroups descend:
`Q j ≤ Q i` if `i ≤ j`. For `i < j < r`, every element of `Q j` must act
on `v i` by some unit of `F` in the actual rational representation.

`exists_simultaneous_min_orbitHeight` produces `q : Q 0` such that, writing
`h = g * rational(q)`, every `i < r` and `s : Q i` satisfy
`orbitHeight(ρ i, v i, h) ≤ orbitHeight(ρ i, v i, h * rational(s))`.
The initial `g` is any actual adelic point. The theorem includes the empty
chain and makes no reductivity, splitting or algebraicity assumption on
the rational subgroups.

`chainHeightMinimalSet` is the subset of `normOneSubgroup F G` where all
these inequalities hold with a specified real factor `c` on the right.
`exists_mul_rational_mem_chainHeightMinimalSet` gives, for every norm-one
`g`, a `q : Q 0` such that `g * rationalNormOne(q)` lies in that set with
`c = 1`. Membership of principal points in the norm-one subgroup is the
published product-formula result.

## Implemented proof

`orbitHeight_mul_rational_eq_of_scalar` first uses the published exact
rational-translation formula. Its scalar hypothesis then reduces the equality
to `PrimitiveAdelicHeight.rationalHeight_smul`. This uses the product formula
for a nonzero rational scalar. Invariance under arbitrary adelic scalars is
neither assumed nor asserted.

For simultaneous minima, induct on the chain length. The empty chain uses the
identity. Given a rational translate satisfying the first `r` inequalities,
use `minimumOrbitTranslate` for the `r`-th representation and subgroup `Q r`.
Call this new factor `p`. Its membership in `Q 0` preserves the stated location
of the accumulated rational translate. The new `r`-th inequality follows from
`minimumOrbitTranslate_min`.

For an earlier index `i < r`, the scalar-action hypothesis preserves its height
at the new point. Since `Q r ≤ Q i`, for every `s : Q i` the product `p * s`
is still in `Q i`. Apply the previously established minimum to `p * s`.
The principal-map homomorphism law and associativity identify its right side
with the required height after translating the new point by `s`. This
preserves all earlier minima. The norm-one corollary coerces the same equation
and uses the principal norm-one map.

## Provenance and remaining obligations

The proof combines the published `AdelicOrbitHeightMinimum` with the published
rational-scalar product formula in `PrimitiveAdelicMinimum`. Springer (1994),
§2.3, printed p.212, is the mathematical context for using a chain of adapted
representations and height-minimal sets. This module is a derived chain lemma,
with the scalar and nesting premises stated explicitly.

The printed formula for the set in §2.3 appears to quantify the rational
translation in `P_i(k)`, while its vector line is stabilized by `P_i`. Such a
translation already preserves the height by the product formula. This module
does not claim a literal transcription of that formula. For the nontrivial
successive-minimum argument, the natural application minimizes the representation
adapted to `P_(i+1)` over the preceding group `P_i(k)`; later subgroups then
preserve earlier heights. The formal statement is independent of this
interpretation of the printed indexing.

The module does not yet construct the chain of adapted representations for
standard parabolics, prove the required scalar/nesting conditions in that case,
compare line characters with simple roots, or prove rank-one reduction and
uniform chamber bounds. It does not prove the chamber-reduction target.

## Source

T. A. Springer, *Reduction theory over global fields*, Proc. Indian Acad.
Sci. (Math. Sci.) 104 (1994), 207–216. Registered source
`springer-1994-reduction-global-fields`, SHA-256
`774f5531200db07140b30ffb8f4adce8cf3a3914ca9f38b796f2a2d24ff18496`.
Context: §1.8, printed pp.209–210, rational scalar invariance and attained
height minima; §2.3, printed p.212, adapted chains and height-minimal sets.
The rendered original p.212 was inspected for the indexing discussion above.
