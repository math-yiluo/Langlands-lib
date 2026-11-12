# Original fixed-base coordinates of algebraic-space adelic stages

This internal supporting construction expresses arithmetic stage topologies
as products of the original local point topologies over the fixed ring of
S-integers.

`fieldValuedBaseChangeHomeomorph` identifies points after base change of a
commutative coefficient ring with the original points, using
`baseChangeRingPointsEquiv`. For a coefficient map to a topological field,
the source has the field-valued topology on the base change and the target
has the field-valued topology along the same map restricted to the original
base ring. The existing base-change identity for the induced topologies
makes this equivalence a homeomorphism.

For a separated finite-type space `X` over the S-integers of a number
field and any enlarged finite support `T` containing `S`,
`AdelicSpaceStageCoordinates.numberFieldStageHomeomorph` identifies the
`T`-stage points with the product of `X`'s points over all original
infinite, finite-field, and completed-integer factors of the `T`-level.
Each factor has its original field-valued topology, restricting the
coefficient action from the T-integers to the original S-integers.
The construction retains the original factor algebra actions and introduces
the analogous restricted action on the completed fields.

The proof composes the defining stage equivalence with the coordinate
homeomorphism for the base-changed model and the product of the field-valued
base-change homeomorphisms. The published arithmetic level point theorem
supplies bijectivity of the middle coordinate map. Base change preserves
the separatedness and finite type needed there.

The component formula is coefficient change along the original level
projection restricted to the fixed base ring. It follows from coefficient
naturality of `baseChangeRingPointsEquiv` and cancellation with the defining
stage equivalence.

The provenance is internal composition of the defining stage topology,
the published level point bijection, and base-change identities. This unit
does not compare global fields or prove the adelic Weil restriction theorem.
