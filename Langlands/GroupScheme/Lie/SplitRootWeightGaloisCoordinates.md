# Galois coordinates on roots of a split maximal torus

This internal deduction removes the dimension-one premise from the
stabilizer-compatible actual Lie coordinate construction when the torus is
maximal in a connected reductive group and splits over the coefficient
field. It uses the published `splitRootLieLine`, connected-reductivity
under field extension, maximal-torus base change, and
`rootWeightEquivariantLinearEquiv`.

Let `k` and `L` be fields in arbitrary universe `u`, with a `k`-algebra
structure on `L`. Let `G/k` be an actual affine connected reductive group,
and let `j : T.toGrp ⟶ G` be an actual maximal torus. Assume its base change
`T_L` is split. For every actual root `beta` of `j_L`,
`finrank_splitRootWeight_eq_one` proves that the original adjoint weight
space of `beta` in the Lie kernel of `G_L` has dimension one over `L`.
The proof transports reductivity and maximality to `L`, applies
`splitRootLieLine` there, and uses its linear equivalence to compute the
dimension. No finiteness assumption on the field extension is needed
for this dimension conclusion.

When `L/k` is finite, `splitRootWeightEquivariantLinearEquiv` is an
`L`-linear equivalence from `L` to that actual adjoint weight space.
It supplies the proved dimension to the existing Hilbert 90 construction.
Its `_galois` theorem states that the canonical actual Lie coefficient
transport by each element of the ordinary root-character stabilizer
agrees with applying that element to the coordinate in `L`. The map and
its law use the same chosen equivalence. No Galois assumption on `L/k`
and no supplied action on the weight space are required.

These are Lie coordinates. This module does not identify the actual root
group with an additive field, prove root-restriction-fiber transitivity,
or construct a globally compatible root valuation system or an apartment.
