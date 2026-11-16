# Actual incident radical images and the full integer-facet parabolic bijection

Module `Langlands.BruhatTits.IntegralModels.UnramifiedIntegerFacetRadicalImages`.
This internal composition works at arbitrary universe `u` and in both
characteristics.

Let `F` be a nonarchimedean local field, `G` an affine group scheme over the
actual maximal unramified field, `E : UnramifiedZeroDatum F G`, and
`C : MaximalUnramified.BuildingData F G`. Supply an actual full-facet family
`M : IntegerFacetModelData C (fixedFieldIntegers F)` with the full neutral
integral-point formula at every original full facet `J`:
`(M.model J).neutral.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer J.val`.
Fix any actual full target facet `Fc` and supplied special-fibre quotient
data `Q` there, and assume `Q.IsReductiveQuotient`.

`UnramifiedIntegerFacetRadicalImagesStatement` concludes two assertions:

* For each actual incident facet `J`, the entire target radical preimage
  `Q.positivePoints` is contained in the source neutral integral-point
  subgroup, and the actual neutral special-fibre image of the specified
  model morphism is parabolic.
* The original `M.HasFacetParabolicOrderBijection Fc Q` holds: the actual
  all-test quotient-image map is a bijection onto parabolic subgroup
  functors and reverses incidence containment.

`unramifiedIntegerFacetRadicalImages` proves this statement. Congruence
containment, image parabolicity, image injectivity and parabolic attainment
are all proved consequences; they are not added hypotheses of this statement.
The model family, its full neutral integral-point formula and the valid
chosen quotient remain supplied.

## Implemented proof

`unramifiedIntegerFacet_positivePoints_le_and_isParabolic` presents the
incident full facets in one actual translated apartment. It transports the
target and source models' generic identifications by the inner automorphism
of the inverse chart translation. The published
`integralPoints_transport_innerIso_same_zeroDatum` identifies their integral
points with the zero fixers of the two full apartment facets. The actual
integral schemes, their special fibres and the specified neutral comparison
map are unchanged. The quotient is transported with its actual radical and
projection unchanged. Smoothness and connectedness of the target special
fibre follow from the supplied relative component models.

Apply the published `unramifiedUpstairsRadicalRootGeneration` to the target
neutral model on the full nonempty apartment facet. It supplies one actual
common centralizer subgroup fixing the whole apartment, and the exact
bound for the entire reduction preimage of the actual radical. The published
`unramifiedIncidentReductionPreimage_le_integralPoints` and incidence of
the apartment facets put this whole subgroup in the actual source neutral
integral points. The published
`unramifiedIncidentImage_isParabolic_of_rootGeneration` uses that same
full radical bound and the actual incident dynamic parabolic to prove
parabolicity of the actual special-fibre image on every scheme test.

The actual special-fibre comparison map is definitionally unchanged by
generic inner transport, so its parabolicity applies to the original
morphism. The transported radical preimage and source integral-point
subgroup are images under the same rational-point isomorphism. Its
injectivity reflects containment back to the original generic group.

`hasUnramifiedIntegerFacetParabolicOrderBijection_of_zeroFixers` uses the
published `congruenceSubgroup_le_positivePoints` to obtain target congruence
containment from the whole radical-preimage containment. Together with the
proved special-fibre image parabolicity, this discharges both remaining
inputs of `hasUnramifiedIntegerFacetParabolicOrderBijection`. That theorem
already proves arbitrary full-facet attainment and injectivity for the same
actual model maps.

The import route includes the separately staged generic root-fixer cleanup
and generic torus-adapter relocation. No prohibited building-descent
statement is used. This unit does not construct the supplied models, prove
the neutral integral-point formula, or establish the host fixed-point
split-torus theorem. Its full facet-parabolic bijection is available for
any actual family satisfying that formula and any valid chosen quotient.
