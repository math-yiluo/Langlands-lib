# Tensor points over a varying common point

Author: Worker 105.

This is derived point-space infrastructure for the fibre-product assertion in
Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Proposition 2.1 and its proof, printed pages 2–3.
Registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

For commutative algebra towers R → C → A,B and an R-algebra S,
`CompatibleAlgPointPair` consists of actual R-algebra maps A → S and
B → S whose restrictions to C agree. There is no fixed C-algebra structure
on S: the common C-valued point varies with the pair. The four coordinate
rings lie in one arbitrary universe and S may lie in an independent universe.

`tensorFiberPointPair` restricts an actual R-algebra map from A ⊗[C] B
to the two factors. The tensor balancing identity proves compatibility.
`tensorFiberPointLift` gives S a temporary C-algebra structure using the
pair's common restriction, uses the actual tensor algebra universal map,
and restricts scalars back to R. Its value on a pure tensor a ⊗ b is
the product of the two point values. `tensorFiberPointEquiv` proves that
these maps are inverse, by induction over sums of pure tensors and preservation of one.

The source point space has its existing evaluation topology. The compatible
pairs have the subspace topology from the product of the two evaluation
point spaces. These topologies are specified independently.
Restriction is continuous for any topology on S. If S has continuous ring
operations, the inverse is continuous: evaluate a pure tensor as a product
of two continuous point evaluations and induct over finite sums of pure
tensors. `tensorFiberPointHomeomorph` packages the resulting homeomorphism.

No topology is imposed on R,C,A,B. Finite generation, Hausdorffness and
locality are not needed. The arbitrary-coordinate-algebra and independent
value-universe scope is a derived extension of the source's finite-type
case. This unit does not identify arbitrary categorical pushout cocones
or actual scheme fibre-product points, and does not assert the complete
axiomatic existence or uniqueness result.
