# Normalized CM specialization of the actual polarized numerical tower

Author: Worker 57.

This internal construction specializes the existing actual Harris numerical
polarized class tower to the normalized CM structure map. The signature charts
are exactly those on `harrisCMSection E (algebraMap L F) τ₀`, where `L` is the
displayed imaginary quadratic CM field and `F` has the existing CM structure.
The actual map `p : S → Spec F` induces the reflex structure
`D.harrisTaylorReflexStructure C p`. This uses the explicitly conjugated
`harrisTaylorReflexToCM` of the imported normalization, with its existing sign.
No independent reflex-field structure map is supplied in this specialization.

`positiveObjectCondition_iff` identifies the positive polarized determinant
predicate at this induced reflex map with the normalized CM determinant
predicate on that same object's actual rational action.
`determinantDimensionCondition_iff` combines this identification with the
existing theorem that the normalized determinant implies the full central
trace. Thus normalized determinant and actual geometric relative dimension
on one object are equivalent to the two tests of the existing numerical
polarized tower on that object.

`classCondition_iff_dimension` identifies the existing numerical class image
with determinant-compatible representatives having the prescribed geometric
dimension. The forward implication takes the dimension conjunct of the same
witness. The reverse implication derives the full all-chart central trace
from its normalized determinant and keeps that witness. It proves no
dimension invariance under arbitrary rational isomorphism.

`forgetCMAction` is an abbreviation of the published
`HarrisCMWeilLevel.forgetCMAction` from `HarrisCMWeilActionProjection`.
The specialized numerical class type is the same as the established CM class
type. The reused map takes the existing actual numerical action-class value of
a polarized numerical class and proves membership in the existing joint
normalized action-class image. It extracts one actual satisfying polarized
representative and uses the determinant-and-dimension equivalence on that
representative's abelian scheme and rational action. Its value is the same
underlying action class as `forgetNumericalAction`; its representative formula
identifies the exact jointly satisfying action. No new quotient relation or
independently supplied target object is introduced.

All original Harris transporter arrows retain this action class, as proved
by extracting a satisfying representative and computing the existing level
map. `forgetCMActionNatTrans` abbreviates the published
`HarrisCMWeilLevel.forgetCMActionNatTrans`, the natural transformation from
the existing specialized numerical polarized tower to the constant functor
on joint normalized action classes. It includes subgroup forgetting and both
existing Hecke legs. The final theorems apply the imported joint-class
invariance results to show that every equivariantly rationally isomorphic
action representative of its value satisfies the normalized determinant and
full central trace. Geometric dimension remains existential.

The actual positive auxiliary involution and Hodge-positive witness, original
opposite-group level index and orbit conventions, actual polarizations and
dual geometry, named tensor and Picard propositions, finite-fibre and torsion
inputs, adelic comparison and ordered-pair dual additivity remain those of
the imported numerical polarized tower. This is a fixed-base, fixed-point
construction and requires no Lie base-change naturality statement.

Provenance is internal: specialize the imported normalized determinant
comparison and central trace theorem, retain the existing image witnesses,
and use the existing transporter and quotient maps. Original arithmetic
and geometric conventions retain their citations in the imported paired
modules. This module supplies no varying-base polarized presheaf,
point independence, successive-base-change coherence, representability,
scheme levels, canonical-model comparison or coefficient descent.
