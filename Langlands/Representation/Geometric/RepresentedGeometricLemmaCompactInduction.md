# Normalized compact induction from the original represented orbit

This internal adapter lifts the actual normalized coefficient comparison to
compactly induced functions on the original target Levi image. The source
is the original projection-kernel coinvariant compact induction from the
full original orbit stabilizer, restricted through the original Levi section
and twisted by the original target inverse half.

The construction uses one component of the previously chosen natural
represented compact-comparison family. Multiplication of the original
compact functions by the target inverse-half character moves that character
inside compact induction. The proved equality of the compact inducing
subgroup with the literal target intersection transports the original
functions without changing their arguments or values. Finally the actual
normalized coefficient equivalence acts on each value.

The target is compact induction from the literal target intersection's copy
inside the original target Levi image, with the published normalized
full-intersection source coefficient. The simultaneous dynamic realization
remains explicit for the original stabilizer geometry. No root-system,
algebraic-character detection or inner target quotient compactness is used
in this intermediate construction.

The provenance is internal: the map is a composition of the implemented
relative integral, scalar multiplication on compact functions, transport
through a proved subgroup equality, and postcomposition by the original
coefficient quotient equivalence.

The subgroup-equality and coefficient-postcomposition helpers are shared as
`CompactNormalizationTransport.subgroupCongr` and `subgroupTransport` in
`Representation/Induction/CompactNormalizationTransport`. These are the same
definitions formerly private to this module, with unchanged types and bodies.

Pointwise evaluation and naturality of the assembled equivalence remain
subsequent work. This unit constructs neither the structural inputs nor the
closed local orbit-comparison proposition.
