# The rational image in positive-dimensional adelic projective space

`AdelicProjectiveRationalImageStatement` is the conjunction of the function-field
and number-field statements that the image of the principal rational-point map
in adelic projective space is proper, is not closed, and is not discrete for its
subspace topology. This is a statement target; its proof is separate.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed p.10, the paragraph preceding Example 4.3 and
Example 4.3, registered as `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

The domain consists of actual relative scheme points of polynomial-Proj
projective n-space over the original global field. The map is scalar extension
along that field's original diagonal into its full adele ring. The target carries
the independently constructed arithmetic projective-model topology. Properness
of the image is expressed by failure of surjectivity; nonclosedness concerns
the range as a subset of the actual adelic point space. Mathlib's `IsDiscrete`
means that this subset with its induced topology has the discrete topology.
The statement negates this property.

Both clauses require `0 < n`, as in the source. Dimension zero is excluded:
its relative projective point sets are singletons. The function-field clause
quantifies over finite constant fields and finite extensions of the specified
rational-function field, with a compatible scalar tower and no separability
assumption. The number-field clause uses full adeles, retaining every infinite
and finite local factor. Both clauses retain arbitrary common universe `u` and
every finite initial arithmetic set, including the empty set.

Density and the compact Hausdorff full-product comparison have separate targets.
The intended proof of nondiscreteness also establishes that the ambient local
projective products have no isolated points. Density and a proper image alone
do not imply nondiscreteness in an arbitrary compact Hausdorff space.
