# Nearby parabolic comparisons of recovered fixed-point models

This module proves, without premises,
`Langlands.Geometry.Building.UnramifiedFixedRecoveredParabolicModelsStatement`.
That is the last model-availability input of the published reduction
`unramifiedFixedDepthZeroOpposite_of_recoveredParabolicModels` (module
`UnramifiedRecoveredDepthZeroOpposite`). The route is internal. It uses the
roles of KP Axiom 4.1.22(2),(4) and of the facet geometry in the proof of KP
Proposition 9.4.9 (Kaletha–Prasad 2023, printed pp. 349–350, PDF pp. 380–381),
but the Lean proof composes Library results and does not follow KP's text.

Throughout, `F` is a nonarchimedean local field, `K = inertiaFixedField F` is
its actual maximal unramified extension, and `A = fixedFieldIntegers F` is the
ring of integers of `K`. `A` is Henselian (`fixedFieldIntegersIsHenselian`) and
its residue field is algebraically closed (`fixedFieldResidueIsAlgClosure`).
The module records these two facts as named local instances.

## Neutral-level exact reduction preimage

`RelativeComponentModelData.neutralHom_imageReductionPreimage_eq_range` holds
over any Henselian local domain `R` with algebraically closed residue field and
fraction field `K`. Take two component-model data `source` and `target` for the
same `K`-group and a generic-identity map `ψ` between their neutral models.
Suppose the congruence subgroup of the target neutral model lies in the
integral points of the source neutral model. Then the subgroup
`ψ.imageReductionPreimage` (from `UnramifiedImagePreimage`) equals the image of
the source sections. This subgroup consists of the target integral sections
whose reduction lies in the rational points of the actual schematic image of the
special-fibre map.

Only the inclusion `⊆` needs proof; the other is
`Hom.sectionRange_le_imageReductionPreimage`. The proof runs as follows.

- The source special fibre is smooth, affine and connected, hence geometrically
  integral (`smoothConnectedAffineGeometry`).
- So the projection onto the schematic image is surjective, and over the
  algebraically closed residue field it is surjective on rational points
  (`GroupScheme.rationalPoints_surjective`).
- Henselian reduction surjectivity of the smooth source model
  (`reduction_surjective`) lifts the residue point to a source section `s`.
- For a target section `x` reducing into the image, `x · ψ(s)⁻¹` lies in the
  target congruence kernel. By hypothesis it is the image of a source section
  `s'` (injectivity of `integralPointMap` and `integralPointMap_identity`).
- Hence `x = ψ(s' s)`.

No full-model map is needed, only the neutral `ψ`.

## Facet-closure comparisons in building data

`unramifiedNeutralFacetClosure_isParabolic_and_preimage` works with
`C : MaximalUnramified.BuildingData F G` and two component-model data `M` and
`M'` over `A`. Their full integral points are the norm-one pointwise fixers of
the singletons `{x}` and `{y}` of the apartment of `C`, with `x` in the closed
facet `facetClosure C.affineRoots y` of `y`. For every generic-identity map `ψ`
from the neutral model of `M'` to that of `M`, it proves two things:

- `IsParabolicSubgroup (SchematicImage.inclusion ψ.specialFibreMap)`;
- `ψ.imageReductionPreimage = (rationalPoints.map ψ.hom).range`.

The facets `facet x` and `facet y` are facets, and `facet x ⊆ facetClosure y`
by `facet_subset_facetClosure_iff`. So `facet x` is a face of `facet y`, and
each singleton lies in its facet. An actual reductive quotient of the special
fibre of `M` exists (`SpecialFibreQuotientData.exists_isReductiveQuotient`,
using perfectness of the algebraically closed residue field). The published
theorem `unramifiedNeutralIncidentImage_isParabolic_of_facet` then gives
parabolicity. The published `unramifiedNeutralIncidentCongruence_le_neutral_of_facet`
gives the congruence containment, and the neutral-level lemma above turns it
into the preimage equality.

## Recovered apartment models

`RecoveredApartmentFixerModels.upper_neutralHom_parabolic_and_preimage` applies
the previous theorem to the upper models of two recovered singleton packages
`X` at `x` and `Y` at `y` of an unramified apartment `D`. Here `x` lies in the
closed facet of `y` for `D.affineRoots`. The building datum is the published
`MaximalUnramified.buildingDataOfApartment hG hiT D C hDC`, whose apartment is
`D` itself. The closed-facet hypothesis is transported to its affine roots by
unfolding this definition.

## Nearby comparisons

`RecoveredFixedNearbyModels.hasParabolicComparisonsNear` proves
`M.HasParabolicComparisonsNear` for every recovered nearby-model package `M` at
a point `x` fixed by every `σ ∈ Aut(K/F)`. For every direction `v` and all
sufficiently small `t`, the actual comparison `M.comparison (t • v)` from the
two-point model at `{x, x_t}` (where `x_t = D.descentTranslate f hS x (t • v)`)
to the singleton model at `x` then has parabolic special-fibre image and exact
reduction preimage. The proof:

1. For each `t`, choose the recovered singleton models `N t` at `x_t`
   (`recoveredFixedPointModelsOfVertexInputs`, with the proved model inputs
   `vertexOneStabilizerMaximalBounded`, `maximalBoundedIntegralModel`,
   `smoothIntersection` and `unramifiedSmoothModelDescent`). The point `x_t` is
   again Galois-fixed (`galois_fixed_descentTranslate`).
2. Near `t = 0`, the two-point and endpoint neutral integral subgroups agree
   (`eventually_source_neutral_integralPoints_eq_endpoint`), and `x` lies in
   the closed facet of `x_t` (`eventually_mem_facetClosure_descentTranslate`).
3. The lower comparison gives the upstairs neutral integral-point inclusion
   (`nonempty_neutralHom_iff` with the proved `unramifiedSmoothHomExtension`).
   The proved `smoothHomExtension`, through `fixedField_hasSmoothHomExtension`,
   extends the generic identity to an actual upstairs neutral map `ψ` from
   `(N t).upper` to `M.target.upper`.
4. The previous section gives parabolicity and the exact preimage for `ψ`. The
   published descent wrappers `hasParabolicSpecialFibreImage_of_unramifiedModels`
   and `hasParabolicReductionPreimage_of_unramifiedModels` transfer both to the
   lower comparison. Their smooth upstairs models and integral-point equalities
   come from the recovery data.

The upstairs comparison uses the endpoint singleton model at `x_t`, not the
two-point model. The facet theorems need the source subset inside one facet,
and only a neutral-level map is available between these models, so the neutral
preimage lemma above is used.

## The statement

`Langlands.Geometry.Building.unramifiedFixedRecoveredParabolicModels` proves
`UnramifiedFixedRecoveredParabolicModelsStatement.{u}` at every universe. For
every fixed point `z`, it takes the published package
`recoveredFixedNearbyModelsOfVertexInputs` with the proved model inputs and the
proved `unramifiedSmoothHomExtension`. It returns the target's lower and upper
models, their recovery and the exact full-fixer equality. The nearby parabolic
root comparisons come from the published
`RecoveredFixedNearbyModels.parabolicRootComparisonsNear` (with reductivity of
`G_K` from `baseChange_of_algebraicExtension`) applied to the theorem above.

No premise or new axiom is added; compilation reports only the standard axioms.
