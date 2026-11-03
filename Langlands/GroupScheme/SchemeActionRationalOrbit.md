# Rational sections in scheme-action orbits

Worker 1460.

This internal derived helper imports the published
`SchemeActionRationalPoints` constructions. It supplies no existence
theorem for a closed orbit or a fixed point.

`exists_rationalPoint_lift_of_mem_range` works for any locally finite type
morphism of schemes `f : Z ⟶ Y` and a `k`-point `y` of `Y`, where `k` is
algebraically closed in arbitrary universe. If the underlying point of `y`
belongs to the image of `f`, the fiber product of `f` and `y` is nonempty.
The pullback projection to `Spec k` is locally of finite type.
The published `nonempty_rationalPoints` produces a section of this fiber
product, whose first projection is a rational lift with `z ≫ f = y`.
No global surjectivity or reducedness is required.

For a group scheme acting on a scheme over any base,
`SchemeAction.rationalOrbit a x` is the set of actual sections `a.act h x`
as `h` varies over sections of the group over the base.
`isFixed_of_fixed_mem_rationalOrbit` says that if one of these sections is
fixed over every test scheme, then `x` is also fixed. Applying `h⁻¹` to
`h · x = y` shows `x = h⁻¹ · y = y`.

Over an algebraically closed field, with the acting group locally of
finite type, `mem_rationalOrbit_iff` identifies rational orbit membership
with membership of the underlying rational point in the image of the
actual orbit morphism. The forward direction evaluates the published
orbit-map formula at the closed point of `Spec k`. For the reverse
direction, the orbit morphism is locally of finite type because its
composite with the structure morphism is the structure morphism of the
acting group. The preceding lift lemma produces an actual group section,
and the orbit-map formula identifies its action with the given section.
The target scheme need not be reduced, separated or locally of finite
type for this argument.

`isFixed_of_fixed_mem_orbitImage` combines this membership comparison
with the group argument. `isFixed_of_closed_orbitImage` additionally
assumes that the orbit image is closed and that a fixed rational point
belongs to its topological closure. Closedness turns this into image
membership, and the preceding lemma concludes fixedness over all test
schemes. Closedness and the fixed point are explicit hypotheses of this
conditional result; their existence remains a geometric obligation.

The provenance is internal: the implementation uses the published
categorical action laws, rational-point existence, and Mathlib's actual
scheme fiber products and their underlying-point lifting property. No
external geometric theorem is assumed or claimed here.
