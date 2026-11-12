# Actual homomorphism descent over arbitrary Galois extensions

This internal construction by Worker 166 descends an actual homomorphism
between scalar extensions of two affine group schemes over a field. The
extension is Galois, with no finite-degree or finite-type assumption. The
explicit compatibility premise says that pulling the homomorphism back along
every field automorphism commutes with the canonical descent isomorphisms.

The actual relative graph is a closed subgroup of the base change of the
original product. Naturality of canonical descent with the two original
product projections proves that the graph inclusion is compatible whenever
the homomorphism is. Its all-test range is consequently invariant, so the
published arbitrary-Galois closed-subgroup descent theorem supplies an actual
closed graph model over the original field, with exact inclusion recovery.

The first projection of this descended graph becomes an isomorphism after
scalar extension. Faithfully flat reflection makes it an isomorphism over the
original field. Composing its inverse with the second projection constructs
an actual homomorphism whose scalar extension is exactly the given one.
Faithfulness of scalar extension proves uniqueness. If the supplied
homomorphism is invertible, reflection also makes the descended homomorphism
invertible, giving the actual isomorphism `Descent.GaloisHom.iso` with exact
recovery.

This is a generic derived construction. It does not assert compatibility of
any particular Weil-restriction comparison or prove the final structure
theorem.
