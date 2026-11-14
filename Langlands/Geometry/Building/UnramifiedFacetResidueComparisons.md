# Canonical maximal-unramified facet residue comparisons

This is an internal specialization of the actual Galois-facet residue model
comparisons to the maximal unramified extension of a nonarchimedean local field.
The universe is arbitrary and both characteristics are allowed. The field is
`LocalGalois.Separable.inertiaFixedField F`, the ring is its actual
`fixedFieldIntegers F`, the integer valuation is
`MaximalUnramified.valuation F`, and the residue algebra is the one induced by
`residueToFixedField F`.

The original apartment data, its Galois stability, connected reductivity after
base change, maximal split torus, actual centralizer, full V6 compatibility,
integer-facet models and exact descriptions of their full integral-point images
remain hypotheses. The images are the character-valuation kernel intersected
with the full original facet's pointwise fixer. A Galois-fixed facet, an actual
special-fibre quotient datum, an affine residue-field group and a specified
quotient base-change isomorphism are also supplied. Neither model existence nor
quotient descent is asserted by this unit.

`FiniteUnramified.fixedResidueAut` induces the automorphism of the actual residue
field from the published `fixedFieldIntegerAut`. It fixes the base residue field:
choose an integer representative in the base and use the field automorphism's
commutation with base scalars. `fixedResidueAction` checks identity and
composition on residue representatives, giving the actual group homomorphism
to residue-field algebra automorphisms. `fixedResidueAction_square` proves the
literal spectrum square between the canonical residue and integer maps by the
same induced-map calculation. This constructs a coefficient action; it is not a
quotient-descent square.

The published `separableUnramifiedArithmetic` supplies the DVR property of the
actual ring. `fixedFieldIntegersIsHenselian` supplies its Henselian property, and
`fixedFieldResidueIsAlgClosure` supplies an algebraically closed, hence separably
closed, residue field. The published
`MaximalUnramified.valuation_galois` supplies valuation invariance. The integral
coefficient automorphism and generic square are exactly the published
`FiniteUnramified.fixedIntegerBaseAut` and `fixedIntegerBaseAut_generic`.

`unramifiedIncidentResidueIso` and `unramifiedFixedFacetResidueIso` use these
proved arithmetic inputs and coefficient maps to specialize the constructed
isomorphisms from `GaloisFacetResidueComparisons`. Their naturality theorem is
the same literal original incidence square with canonical coefficients.
No strict-ring property, valuation covariance, integral/residue automorphism,
coefficient square or model-comparison isomorphism is supplied as an extra
hypothesis to this specialization.

`UnramifiedFixedFacetResidueQuotientSquare` is the remaining explicit morphism
equality for the constructed fixed-facet comparison, the actual quotient
projection and the specified quotient identification. Its other path is the
base change of that projection and identification followed by the canonical
descent comparison of the residue-field group.
`unramifiedResidueCoefficientComparisons` fills all comparison fields using the
constructed isomorphisms, the proved incidence square and this separate quotient
square. `UnramifiedFacetResidueComparisonsStatement` states that the quotient
square implies nonemptiness of those actual comparison data and
`HasGaloisResidueImageCompatibility`. The proving theorem invokes the existing
schematic-image covariance theorem; the conclusion is equality on all test
schemes of the represented incident image subgroup functors.

This derived unit follows the cited Library constructions and arithmetic proofs;
it claims no additional literature theorem. The literal quotient square, actual
facet-parabolic correspondence, model existence and point descriptions, torus
lifting, segment comparison and the unconditional prescribed-point split-torus
theorem remain obligations of the host task.
