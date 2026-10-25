# The fixed field of an actual cocharacter conjugacy class

This module starts with the published rational unitary similitude group and
its iterated complex pullback, retaining the actual central-simple unitary
datum and scalar towers. A cocharacter is a morphism of group schemes from
the multiplicative group over `Spec ℂ` to that complex group.

`galoisCocharacter_conjugate` proves that the published rational Galois
transport preserves inner conjugacy. It passes to the direct rational
pullback, uses the generic base-change and descent result in
`ConjugacyBaseChange`, and returns through the canonical comparison.
Applying the same result to the inverse automorphism and using the
published transport composition law proves `galoisCocharacter_conjugate_iff`.

For a cocharacter `χ`, `complexCocharacterStabilizer χ` is the subgroup of
all rational algebra automorphisms of `ℂ` whose transport of `χ` is
inner-conjugate to `χ`. The conjugacy assertion is an equality of scheme
morphisms witnessed by one complex point of the group. The subgroup laws
are proved: identity uses identity transport; multiplication transports
one conjugacy and composes it with the other; inverse closure transports
by the inverse automorphism and reverses the resulting conjugacy.
`mem_complexCocharacterStabilizer` exposes this membership condition.
Conjugate cocharacters have equal stabilizers, as proved by composing with
the original conjugacy and its transported inverse.

`complexCocharacterFixedField χ` is the actual intermediate field of `ℂ/ℚ`
fixed by that subgroup, using `IntermediateField.fixedField`. Its
membership theorem states that a complex number is fixed by every
automorphism preserving the cocharacter class. Equality of stabilizers
proves that the field is unchanged when `χ` is replaced by a conjugate.

For Harris signature charts `C`, `kottwitzCocharacterReflexField C`
specializes this construction to `kottwitzCocharacter C true`, the
first-factor cocharacter with the existing Kottwitz convention. This is
the fixed-field construction from the actual scheme conjugacy class.
It is not yet identified here with the earlier fixed field of the
numerical Hodge function. That comparison requires the separately stated
`ComplexCocharacterReflexStabilizer` theorem. No finiteness, number-field
instance, canonical model, or descent of a Shimura variety is asserted.

The content is an internal construction from the published Galois action,
scheme conjugacy relation, their base-change compatibility, and Mathlib's
fixed-field operation. It does not assume the numerical stabilizer
comparison or any unpublished matrix-innerness or point-detection proof.
