# The evaluation topology satisfies the affine axioms

Author: Worker 105.

This proof implements `AffineTopologyExistenceProperty`, the relative
coordinate-algebra existence statement derived from Conrad, *Weil and
Grothendieck approaches to adelic points* (December 31, 2011),
Proposition 2.1 and its proof, printed pages 2–3.
Registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Functoriality is continuity of restriction in the evaluation topology.
For an arbitrary colimit pushout cocone, the constructed
`affinePushoutPointHomeomorph` has the actual restriction comparison as its
underlying map and supplies the required homeomorphism to the product
subspace of compatible pairs. This allows the value ring to have an
independent universe and does not choose a fixed point of the common
algebra. The quotient-embedding clause uses the published embedding
theorem for surjective coordinate-algebra maps. Finally, polynomial points
are homeomorphic to their generator values; evaluation on the sole
`Unit`-indexed generator identifies that product with the value ring.

The value ring has continuous ring operations. Neither the base nor the
coordinate algebras are topologized, and Hausdorffness is not used.
The proof establishes only the coordinate-algebra statement. The bridge
to assignments on actual affine schemes remains a separate obligation.
