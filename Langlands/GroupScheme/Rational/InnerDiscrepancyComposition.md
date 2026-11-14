# Composition and comparison of local families with inner discrepancy

Worker 692.

This is an internal formal transport result for local group isomorphisms over
an arbitrary scheme `S`. It combines the published `LocalGroupIso`,
`InnerDiscrepancy`, `InnerDiscrepancySymmetry` and
`InnerDiscrepancyRefinement` interfaces. It is derived from those definitions
and their proved lemmas, rather than transcribed from a separate literature
statement.

The namespace is `Langlands.GroupScheme.LocalGroupIso`. The construction
`trans e f` composes families `e : G → H` and `f : H → K` on a common cover;
`compare e f` is `e.symm.trans f` for two families with common source `G`.
The constructions are natural on all relative test schemes. The versions
`transOnProduct` and `compareOnProduct` first refine the two covers to their
fibre product.

## Equivariance and discrepancy formulas

Let `a` be an automorphic action of `A` on `G`, `b` an action of `B` on `H`,
and `d : LocalGroupIso A B U`. Assume explicitly that `e` intertwines the
actions through `d`, on every relative test scheme and every point `c` of `U`:

`e_c(a_x(g)) = b_{d_c(x)}(e_c(g))`.

The theorem `symm_equivariant` proves the inverse equivariance equation by
applying the injective equivalence `e_c` and then the displayed equation.

Suppose `x` represents the discrepancy of `e` between `c,c'`, so that
`e_c(a_x(g)) = e_c'(g)` after every refinement. If `y` represents the
discrepancy of `f : H → K` for the action `b`, then

`d_c⁻¹(y) * x`

represents the discrepancy of `trans e f` for `a`. This is
`RepresentsDiscrepancy.trans_of_equivariant`. Its proof uses preservation of
products under pullback, the action's product equation, equivariance,
naturality of `d`, and the two discrepancy equations, in that order.
The theorem `HasInnerDiscrepancy.trans_of_equivariant` chooses the two
representing points and applies this formula.

For two families `e : G → H` and `f : G → K` with the same source, let `x,y`
represent their respective discrepancies for `a`. Then

`d_c(y * x⁻¹)`

represents the discrepancy of `compare e f` for `b`. The theorem
`RepresentsDiscrepancy.compare_of_equivariant` applies the published inverse
discrepancy formula and the composition formula above, using
`symm_equivariant` and preservation of products by `d_c`.
`HasInnerDiscrepancy.compare_of_equivariant` follows by choosing `x,y`.

## Distinct covers and scope

The two `HasInnerDiscrepancy` theorems ending in `OnProduct_of_equivariant`
apply the common-cover results to the pullbacks along the two fibre-product
projections. They use the published preservation of innerness under
refinement. The action-intertwining hypothesis pulls back by substitution.

No faithful-action, reductivity, étale, surjectivity or finiteness assumption
is required for these transport results. The module does not construct the
local acting-group isomorphism `d`, nor prove equivariance for adjoint
quotients. In particular, it does not by itself establish symmetry or
transitivity for all inner forms in the semi-local target, or prove existence
or uniqueness of quasi-split inner forms.
