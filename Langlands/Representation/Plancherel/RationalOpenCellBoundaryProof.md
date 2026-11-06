# The algebraic boundary of the actual rational dynamic open cell

Author: Worker 135.

The theorem `Langlands.Plancherel.rationalDynamicOpenCellBoundary` proves
`RationalDynamicOpenCellBoundaryStatement.{u}` over every field in an
arbitrary universe. It uses the actual smooth affine group scheme, dynamic
subgroup functors and rational points named by the published proposition.
It requires no connectedness, reductivity, splitness, characteristic or
local-field hypothesis beyond the statement's smoothness and affineness.

This is an internal consequence of the published opposite multiplication
open immersion, scheme inversion and the lift property of open immersions.
No separate assertion from external literature is claimed.

The helper `rationalPoint_mem_range_iff` proves that a rational point lands
in the underlying range of an open immersion precisely when it factors
through that immersion. Since the spectrum of a field has a unique point,
the range condition at the chosen closed point controls the entire image
of the rational-point morphism. The open-immersion lift supplies the
factorization. Composing the lift with the structure morphism verifies
that it is over the original field spectrum. Conversely, a factorization
gives a witness in the underlying range by evaluation.

The helper `range_inverse_opposite_multiplication` treats two represented
subgroup functors. On rational points the inverse of multiplication sends
`(u,p)` to `p⁻¹*u⁻¹`. Both subgroups are closed under inversion, so the
result is a value of the required map `(p,v) ↦ p*v⁻¹`. Conversely, for a
value `p*v⁻¹`, represent `v` and `p⁻¹` by rational points of their subgroup
schemes and take their categorical product lift. Inverse multiplication
at this lift is the given value. Thus the image identification uses the
actual represented subgroup carriers on the identity test object.

The main proof chooses the published affine representatives of the dynamic
opposite unipotent subgroup and parabolic subgroup. The published
`oppositeCellStatement` makes their multiplication an open immersion.
Scheme inversion is an isomorphism, so composing with it is still an open
immersion. The two helpers identify the inverse image of its underlying
range under actual rational-point evaluation with the required rational
cell range. Let `Z` be the complement of that underlying range. It is
Zariski closed because an open immersion has open range. It is proper
because the identity rational point is the cell value at `(1,1)`.
Preimages commute with complements, giving exactly the target equality.

This geometric result supplies no Haar nullness or conullness conclusion.
The actual local-density, equivariance and measure arguments are separate
obligations of the parent task.
