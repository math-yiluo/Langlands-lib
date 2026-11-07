# Geometrically connected arithmetic models without a common fibre dimension

This derived statement isolates the model-enlargement step at the start of
Conrad's Theorem 4.5 proof (printed p.12), using Theorem 3.4(2) and the
integer-ring interpretation of Remark 3.5 (printed pp.5–6). Source:
Brian Conrad, *Weil and Grothendieck approaches to adelic points*,
December 31, 2011, registered as
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Each arithmetic branch has three clauses, using the published actual
integer-ring and compatible-model templates:

1. For every pair of finite-type models over an initial integer ring and
   every morphism between them, geometric connectedness of its generic
   fibre is equivalent to geometric connectedness after base change to
   some finite exceptional superset.
2. The same equivalence holds for smoothness and geometric connectedness
   together, at one common enlarged level.
3. Every smooth geometrically connected morphism between separated
   finite-type schemes over the field has compatible separated
   finite-type models over some integer level above any prescribed finite
   exceptional set. The model morphism is smooth and geometrically
   connected. The actual generic-fibre isomorphisms identify this
   morphism with the original field morphism through the specified
   commuting square.

The first two clauses require no separatedness or affineness of the
supplied models. The third retains separatedness of both original field
schemes and of both resulting models. Function fields use the actual
places of the published curve construction, a perfect constant field,
and a finite function-field extension. Number fields use their original
finite places and outside-set integer subrings. Every object has the
arbitrary common universe `u`; there is no restriction to universe zero
or finite sets of places of any fixed size.

Mathlib's `GeometricallyConnected` convention includes nonempty geometric
fibres, so the assertions retain the source's surjectivity and
nonemptiness. No fibre dimension is supplied or asserted to be constant
across target components. This is a derived strengthening of the
previous fixed-dimension model statements: general constructibility of
the geometric-connectedness fibre locus permits descent without the
pure-dimension conjunct. The compatible-model clause is exactly the
smooth surjective geometrically connected model step used on printed
p.12 before the componentwise dimension reduction.

These are proposition definitions, not proofs. This unit does not prove
Lang–Weil, integral-point lifting, local openness, or adelic openness.
