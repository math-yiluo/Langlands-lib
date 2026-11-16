# Smooth actual homogeneous quotient actions

This internal adapter reuses the existing `Dynamic.flagQuotientSchemeAction`
for a supplied actual homogeneous quotient. It defines `action` and the
`identityCoset` section, retains multiplication followed by the supplied
projection on every lifted test point, and proves that the actual action
relation is smooth. The embedded subgroup fixes the identity coset after every
relative test refinement. If the ambient group is smooth over the base, the
same supplied quotient is smooth over the base.

The generic relation result assumes a smooth, surjective, quasi-compact actual
projection with exact coset fibers on every relative scheme test. It works over
any base scheme, in every universe. Precomposing the relation with the smooth
surjective map `G × G → G × Q` gives the composite of the group shear
`(g,h) ↦ (g h,h)` and `q × q`. Both the shear and the two smooth quotient maps
are actual scheme morphisms. Smoothness of the composite descends along the
smooth surjective source cover. The structure smoothness result uses the same
source descent on the quotient projection. The fixedness assertion uses the
supplied all-test coset equation, with the inverse of the subgroup point as
its witness.

The provenance is internal composition of the published quotient action,
actual group shear and smooth source descent. No quotient existence,
affineness, properness or reductivity theorem is asserted here.
