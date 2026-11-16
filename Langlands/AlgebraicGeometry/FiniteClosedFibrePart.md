# Maps into a supplied finite closed-fibre part

This internal module works over any commutative local ring `R : Type u`.
It assumes an actual open `U` of `X` satisfying
`IsFiniteClosedFibrePart f U`; it does not use or prove
`HenselianFinitePartStatement`.

Every map `g : Y → X` over `Spec R` from a universally closed `Y → Spec R`
has image in `U`. Apply the published
`open_eq_top_of_contains_closedFibre` to the inverse image open `g⁻¹(U)`.
Its closed fibre is the whole closed fibre of `Y`, since `U` contains the
whole closed fibre of `X`. The resulting equality with the top open gives
the asserted image containment. In particular this applies to every finite
`Y` over `R`.

`IsFiniteClosedFibrePart.lift` is the actual scheme morphism `Y → U`,
constructed by the open-immersion lifting operation. `lift_fac` identifies
its composite with the original `g`; `lift_over` records its compatibility
with the base map; `lift_unique` follows by cancellation of the open
immersion. Applying image containment to the inclusion of each of two finite
closed-fibre parts into `X` proves equality of the two opens (`eq`).

The proof is source-free composition of the published closed-fibre cover
lemma and Mathlib's open-immersion and finite-morphism APIs. It constructs
no finite part, group law or normal subgroup.
