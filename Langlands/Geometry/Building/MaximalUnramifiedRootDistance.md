# The invariant root distance on every supplied maximal-unramified building

For any nonarchimedean local field `F : Type u`, affine group scheme `H` over
`K = inertiaFixedField F`, and supplied `B : MaximalUnramified.BuildingData F H`,
this module defines `B.invariantRootDistance` on the existing quotient
`B.ReducedBuilding`. All declarations are at arbitrary universe `u`, with no
restriction on equal or mixed characteristic and no additional hypothesis on `B`.
The declarations lie in namespace `MaximalUnramified.BuildingData`.

The definition specializes `KPApartmentData.chosenRootDistance` to `B.apartment`.
The published theorem `MaximalUnramified.commonApartments` supplies common
translated-apartment coordinates. Finiteness of the actual relative roots follows from
`finite_relativeRoots` for the supplied maximal split torus of the connected
reductive group. The distance is the canonical root norm of the difference
of those coordinates; it retains the original quotient and rational-point action.

`invariantRootDistance_smul` proves invariance under that action.
`invariantRootDistance_smul_apartmentMap` identifies the distance in any translated
original apartment with the prescribed square root of the sum of the squared root evaluations of
`a -ᵥ b`. This explicit formula is definitionally
`B.apartment.rootDistance a b` from `UnramifiedBuildingMetricReduction`.
`invariantRootDistance_apartmentMap` is its original-apartment specialization.
These results provide clauses 1 and 2 of the published
`MaximalUnramified.RetractionDistanceStatement`, for a fixed explicit function.

`eq_invariantRootDistance_of_invariant` shows that any function with those two
properties equals this function: place a pair in a common translated apartment,
use invariance to remove the translate, and use the apartment formula.
Consequently a retraction construction may use this explicit distance or any
function satisfying the same two properties.

This is an internal specialization of the algebraic coordinate-independence
construction in `ApartmentQuotientRootDistance`, the proved common-apartment
coverage in `IntegerValuationCommonApartmentsProof`, and the algebraic
finite-root theorem. The module uses the explicit root-sum formula so that it
does not import the downstream descent statements reached through
`UnramifiedBuildingMetricReduction`. It introduces
no new source assertion. It does not construct retractions, prove the triangle
inequality or construct a complete NPC metric. Clause 3 of
`RetractionDistanceStatement`, and the actual coherent coefficient action with
finite orbits in `UnramifiedSemilinearMetricActionStatement`, remain separate
obligations.
