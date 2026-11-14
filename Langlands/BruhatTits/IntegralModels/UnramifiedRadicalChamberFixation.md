# Chamber fixation by the depth-zero reduction kernel

This module is internal and derived from published Library results. It takes the
full upstairs radical-generation statement
`UnramifiedUpstairsRadicalRootGenerationStatement` as an explicit premise, and
the transitivity of the depth-zero point fixer on chambers as another
explicit premise. Neither premise is proved here, and nothing is attributed
to a numbered result of the literature. Informally, the result is the
familiar fact that the depth-zero reduction kernel of a parahoric at a
point acts trivially on the chambers whose closures contain that point. It
is assembled here from the Library's radical-image bounds and the
`G(K)^{0+}` description of that kernel.

## Generic building lemmas

Let k be a field with an integer-valued valuation v, G an affine group
scheme over k, and B any supplied `IntegerValuationBuildingData v G`.

* `IntegerValuationBuildingData.kernel_stabilizes_of_transitive` is pure
  group theory. Let P be a subgroup of G(k), q : P →* M a homomorphism to a
  group M in any universe, and y a point of the reduced building. Let Y₀ be
  a chamber closure presentation through y, and assume every element of
  ker q maps Y₀ onto itself as a set. Assume also that for any two chambers
  Y, Y' presented through y, some h ∈ P satisfies Y' = h · Y. Then every
  element of ker q maps every chamber presented through y onto itself.
  Proof: write Y = h · Y₀. For g ∈ ker q, the conjugate h⁻¹ g h is again in
  ker q, so it stabilizes Y₀, and hence g stabilizes h · Y₀.
* `IntegerValuationBuildingData.smul_image_eq_of_mem_pointwiseFixer`: an
  element of the pointwise fixer of a subset Y maps Y onto itself.
* `IntegerValuationBuildingData.exists_standard_chamberClosurePresentation`:
  for every apartment point x there is a regular point x₀ (no affine root
  vanishes at x₀) with x in the closure of the facet of x₀. The image of
  that facet under `apartmentMap` has a chamber closure presentation through
  `apartmentMap x`, with group element 1. Regularity and the closure
  condition come from the published
  `exists_regularPoint_closure` for the locally finite reflection
  arrangement. That arrangement is supplied by
  `isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs`.

## Unramified kernel fixation

Now let F be a nonarchimedean local field in universe u, K its inertia fixed
field, O the fixed-field integer ring and k_O its residue field. Let G be an
affine group scheme over K, C a `MaximalUnramified.BuildingData F G` and E an
`UnramifiedZeroDatum F G`. Throughout, `hRad` is the premise
`UnramifiedUpstairsRadicalRootGenerationStatement.{u}`.

* `unramifiedRadicalPreimage_le_zeroFixer_facet`. Assume `hRad`, and let x lie
  in the closure of the facet of x₀. Let N be a smooth integral model of G over
  O whose integral points equal E's zero subgroup intersected with the
  pointwise fixer of `{apartmentMap x}`. Let `i : U ⟶ N.specialFibre`
  represent its unipotent radical. Then the generic image of the reduction
  preimage of the rational points of U lies in E's zero subgroup intersected
  with the pointwise fixer of the image of the facet of x₀.
  Proof: `hRad`, applied to Ω = {x}, which is nonempty and lies in the facet
  of x, writes that group as H ⊔ ⨆ₐ `rootFixerPlus` a {x}, where H fixes the
  apartment pointwise and lies in E's zero subgroup. The published
  `unramifiedIncidentGeneratedGroup_le_zeroFixer` bounds this join by the
  stated zero fixer. It applies because the facet of x is a face of the
  facet of x₀ (`facet_subset_facetClosure_iff`).
* `parahoricReduction_ker_le_zeroFixer_facet`. Let D be a
  `RelativeComponentModelData` over (O, K) for G whose neutral integral
  points equal E's zero subgroup intersected with the pointwise fixer of
  `{apartmentMap x}`. Let Q be `SpecialFibreQuotientData D` whose radical
  inclusion is a unipotent radical and whose projection is an fppf quotient
  by that radical. Assume `hRad` and that x lies in the closure of the facet
  of x₀. Then every element g of `D.neutral.integralPoints` with
  `Q.parahoricReduction g = 1` lies in E's zero subgroup and fixes the image
  of the facet of x₀ pointwise. Proof: the published
  `ker_parahoricReduction` identifies the kernel with the positive points,
  which are the reduction preimage of the radical. The preceding lemma then
  applies to the smooth neutral model `D.neutral`.
* `parahoricReduction_ker_stabilizes_presented`. Make the same assumptions on
  D and Q and assume `hRad`. Let q : `D.neutral.integralPoints` →* M be any
  homomorphism whose kernel lies in the kernel of `Q.parahoricReduction`.
  Assume that for any two chambers Y, Y' presented through `apartmentMap x`,
  some h in E's zero subgroup that fixes `apartmentMap x` satisfies
  h · Y = Y'. Then every g with q g = 1 maps every chamber presented
  through `apartmentMap x` onto itself.
  Proof: choose the standard chamber Y₀ through `apartmentMap x` from
  `exists_standard_chamberClosurePresentation`. The preceding lemma shows
  that ker q fixes Y₀ pointwise, so it stabilizes Y₀. The assumed
  transporters lie in `D.neutral.integralPoints` by the description of its
  points (`pointwiseFixer` of a singleton is the point fixer).
  `kernel_stabilizes_of_transitive` concludes.

## Statement

`UnramifiedRadicalChamberFixationStatement.{u}` is the Prop-valued packaging of
the last lemma. It assumes `UnramifiedUpstairsRadicalRootGenerationStatement.{u}`.
Then for every nonarchimedean local field F in universe u, every affine group
scheme G over K and every supplied C and E, every apartment point x, and every D
and Q satisfying the three conditions above, the following holds. Let M be a
group in universe u and q : `D.neutral.integralPoints` →* M a homomorphism
whose kernel lies in that of `Q.parahoricReduction`. Assume the transitivity
premise: for any two chambers Y, Y' presented through `apartmentMap x`, some
h ∈ E.zeroPoints ⊓ `C.fixer (apartmentMap x)` satisfies h · Y = Y'. Then
every g with q g = 1 maps every chamber presented through `apartmentMap x`
onto itself. `unramifiedRadicalChamberFixation` proves it by applying
`parahoricReduction_ker_stabilizes_presented`. The only axioms are propext,
Classical.choice and Quot.sound.

The transitivity premise has exactly the form of the conclusion of
`UnramifiedZeroDatum.exists_zeroPoints_fixer_smul_chamber_eq` in Worker
5428's candidate `SharpChamberClosureOrbit` (9f576daa, accepted but not
yet published). This module does not import that candidate.

## Role and limits

This is the kernel-fixation part of a proof of
`UnramifiedTwistedResidueQuotientStatement`, for a point of the form
`apartmentMap x`. The module does not construct the model D (compare the
unproved `UnramifiedParahoricModelStatement`) or the quotient Q. It provides
no Frobenius descent of the quotient, and it does not prove `hRad`.

Set stability of a pointwise-fixed subset reuses the generic theorem in [PointwiseFixerSetStabilizer](../../Geometry/Building/PointwiseFixerSetStabilizer.md).
