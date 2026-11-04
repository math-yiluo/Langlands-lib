# Action kernels and normal subgroup fixedness on dominant orbits

This internal helper defines the full action-kernel subgroup functor for an
actual group-scheme action over any base scheme. A point belongs to the kernel
when, after every refinement of its test scheme, it acts trivially on every
point of the acted-on scheme. The definition does not assert representability.
The action laws prove closure under multiplication and inverse, compatibility
with refinements, and normality on every test scheme.
`range_le_kernel_iff` identifies containment of an actual homomorphism's range
in this kernel with equality of its restricted action and the second projection.

For an actual homomorphism `j : H → G` with normal range, if `H` fixes a base
section `x` on all tests, it fixes the entire orbit of `x` on all tests.
Normality writes `g⁻¹ j(h) g` as `j(h')`; the action identity then gives
`j(h) · (g · x) = g · (j(h') · x) = g · x`.

Over any field in universe `u`, assume `H` is smooth and the acted-on scheme `X`
is reduced, separated, and locally of finite type. If the actual orbit map of
`x` is dominant and quasi-compact, the restricted action morphism
`H × X → X` equals the second projection. This conclusion is a morphism
identity, so applies to all points of every test scheme, including nonreduced
and nonaffine tests. No algebraic-closure or characteristic assumption is used.
`range_le_kernel_of_dominant_orbit` expresses the same conclusion as containment
in the full kernel. Neither closedness nor monicity of `j`, nor smoothness of
`G`, is assumed.

The proof first establishes equality after pullback along `H × G → H × X`
using the preceding all-test orbit identity. The orbit map is schematically
dominant because its target is reduced. Its product with `H` stays
schematically dominant under the flat second projection, and stays
quasi-compact. Consequently that product map is dominant. Smoothness of `H`
gives geometric reducedness; local finite type and reducedness of `X` make
`H × X` reduced. The separated-target extensionality theorem extends the
equality from this dominant map.

The construction and deductions are internal consequences of the published
`SchemeAction`, `SchemeActionRationalPoints`, `SubgroupFunctor`, and
`SmoothReducedProof` interfaces, together with Mathlib's flat base change of
schematic dominance and reduced-source separated-target extensionality.
This unit does not prove positive-root uniqueness or supply the remaining
Borel, quotient-dimension, or curve-to-root comparison arguments.
