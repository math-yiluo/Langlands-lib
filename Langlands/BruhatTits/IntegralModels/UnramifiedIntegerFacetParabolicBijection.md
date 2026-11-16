# The actual integer-facet parabolic bijection from explicit model inputs

Module `Langlands.BruhatTits.IntegralModels.UnramifiedIntegerFacetParabolicBijection`.
This internal unit allows arbitrary universe `u` and both characteristics.

Let `F` be a nonarchimedean local field, `H` an affine group scheme over the
actual maximal unramified field, `E : UnramifiedZeroDatum F H`, and
`C : MaximalUnramified.BuildingData F H`. Let `M` be supplied actual full-facet
relative component models over `fixedFieldIntegers F`. The common hypothesis
is the full neutral integral-point formula, for every full facet `J`:
`(M.model J).neutral.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer J.val`.
Fix any full target facet `Fc`, including outside the chosen apartment, and
supplied special-fibre quotient data `Q` at `Fc`.

`exists_incidentIntegerFacet_quotientImage_eq_parabolic` proves that, when
`Q.IsReductiveQuotient`, every actual parabolic inclusion into `Q.quotient`
is the actual quotient image of one incident full-facet model. The equality
is equality of subgroup functors on all test schemes. Consequently
`unramifiedIncidentParabolicImage_surjOn` proves attainment of every parabolic
subgroup functor by the original `M.incidentParabolicImage Fc Q`.

`UnramifiedIntegerFacetParabolicBijectionStatement` additionally retains the
target congruence subgroup's containment in every incident source neutral
integral-point subgroup, and parabolicity of all the actual source-to-target
neutral special-fibre images. Under these explicit inputs it concludes the
existing `M.HasFacetParabolicOrderBijection Fc Q`: the actual image map is a
bijection onto parabolic subgroup functors and reverses incidence containment.
`unramifiedIntegerFacetParabolicBijection` proves this Prop-valued statement.

## Implemented proof

The preliminary `IntegerValuationBuildingData.facetTranslateEquiv` transports
full facets under the original rational-point action. Its inverse is transport
by the inverse group element. The value formula and inverse identity are
immediate; `facetPrecedes_translate` translates a common apartment chart, and
`buildingFacetAt_eq_translate` uses the published full-facet partition. These
are the integer-valued counterparts of the published local-field
`BuildingFacetAction` constructions, using the integer-building facet APIs.
No local-field structure on the maximal unramified field is assumed.

For attainment, present `Fc` in a translated apartment, through `g` and `x`.
The published no-inversions theorem identifies the neutral full-facet zero
fixer with the singleton zero fixer at `g • apartmentMap x`. Transport the
target model and its quotient by the generic inner automorphism of `g⁻¹`.
This changes the generic identifications while keeping the actual integral
schemes, special fibres, quotient and projection literally the same. The
published `integralPoints_transport_eq_translated_zeroFixer` identifies its
neutral integral points with the apartment-point zero fixer at `x`.

Apply the published `exists_incidentFacet_model_quotientImage_eq_parabolic`
to this transported target. Its two statement inputs are discharged by the
published `unramifiedRootPositiveReduction` and
`MaximalUnramified.zeroFacetNoInversions`. Translate its resulting full source
facet back by `g`. Translation of the common apartment chart gives original
incidence above `Fc`. Transport the supplied neutral model of that translated
facet by the same generic inner automorphism of `g⁻¹`. Its actual integral
points have the required zero-fixer characterization, and smoothness comes
from the supplied component data. Geometric connectedness is the published
`neutral_geometricallyConnected`; no extra assumption is introduced. Transport
the actual incidence morphism likewise. The published attainment conclusion
then applies to precisely this morphism, and its all-test quotient image is
literally the original `M.incidentParabolicImage`.

Finally the proved `unramifiedIntegerFacetImageRecovery` supplies image
parabolicity and injectivity from the explicit model, congruence and
parabolicity inputs. Combine these with the proved surjectivity. The existing
`hasFacetParabolicOrderBijection_iff_bijOn` supplies the original reversed
containment clause from actual model-map composition.

The clean positive-root proof provider uses the separate generic torus-adapter
relocation, and image recovery uses the separate generic root-fixer import
cleanup. No prohibited building-descent statement is a proof input.
This unit does not construct the actual model family, prove its neutral
zero-fixer formula, prove target congruence containment or actual special-fibre
image parabolicity, or establish the host fixed-point split-torus theorem.
