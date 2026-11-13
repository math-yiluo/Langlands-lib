# Full special-fibre reduction and pro-p radical preimages

Worker 302 supplies an internal construction of full special-fibre reduction on
the neutral integral-point image and proves the pro-p property of the actual
radical preimage. All declarations work at arbitrary universe `u`.

For supplied `RelativeComponentModelData D` over a local domain `R` with fraction
field `K`, `D.neutralSpecialReduction` sends a point in
`D.neutral.integralPoints` to its point in the actual full residue special fibre.
It transports the published reduction on integral sections through the inverse
of `D.neutralSectionsEquiv`. Its kernel is the actual congruence subgroup viewed
inside the neutral integral-point image. For supplied quotient data `Q`, the
inverse image of `Q.radicalPoints` is
`Q.positivePoints.subgroupOf D.neutral.integralPoints`. Both identities follow
from the injectivity of the actual integral-point map; no quotient validity or
surjectivity is needed.

Over a nonarchimedean local field `F`, the full reduction kernel is pro-p for
`p = ringChar` of the actual residue field. The proof transports
`IntegralModel.localField_isProP_congruenceSubgroup` to the neutral ambient group.
If the specified radical is an `IsUnipotentRadical`, smoothness supplies local
finite type and its closed inclusion in the affine special fibre supplies
affineness. `isPGroup_range_testPoints_of_isUnipotent` then proves that its
actual residue-field image is a p-group.

The positive subgroup is compact by
`Q.localField_isCompact_positivePoints`. The subgroup equivalence inside the
neutral integral-point image preserves compactness, and total disconnectedness
is inherited from the canonical affine rational-point topology.
`IsProPSubgroup.comap_of_isPGroup` applies to full reduction and the radical's
point subgroup. The inverse-image identity and subgroup topology transport
return the conclusion to the original rational-point group.

`localFieldPositiveProP` has exactly the type of the published
`LocalFieldPositiveProPStatement`; the component theorem actually needs only
the radical property in `Q.IsReductiveQuotient`. This is a derived construction
and proof from the named integral-model, unipotent-point and abstract pro-p
results. It constructs no model or radical and assumes no extra filtration or
pro-p premise.
