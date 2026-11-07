# Weil equivalence of isomorphic p-adic fields

Author: Worker 1693. Internal infrastructure for the proof of
`Langlands.Global.HenniartGlobalizationStatement`.

This module proves the isomorphism property of the actual completion transport
already defined by the globalization target. It introduces no arithmetic
existence assertion and no additional hypothesis of that target. Its provenance
is the published local Weil maps, their embedding and index theorems, and the
existing equivalence on continuous exact virtual groups.

For arbitrary p-adic fields `F` and `E` and a `Padic p`-algebra isomorphism
`f : F.Carrier ≃ₐ[Padic p] E.Carrier`, the theorem
`Langlands.Weil.Local.extensionDegree_algEquiv` proves that the extension degree
of `f.toAlgHom` is one. The proof compares the tower-law formula
`finrank_mul_extensionDegree` with the equality of finite dimensions supplied by
`f.toLinearEquiv`, and cancels the positive dimension of `F`.

`extensionWeilMap_algEquiv_bijective` combines the published injectivity of the
actual map `extensionWeilMap F E f.toAlgHom : W_E → W_F` with its image-index
formula. An index-one subgroup is the whole group, so the map is surjective.
`extensionWeilEquivOfAlgEquiv` equips this same map with its inverse and inverse
continuity. The latter follows from the existing embedding theorem: composing
the inverse with the forward map is the identity. The inverse is chosen as the
inverse of this actual map; the construction does not require a strict
functoriality identity for separately chosen algebraic-closure embeddings.
The forward map and its continuous homomorphism are definitionally the original
`extensionWeilMap`, as recorded by the two comparison lemmas.

For a number field, a finite place `v`, a residue-prime equality `h`, a p-adic
field `K` and the algebra isomorphism `f : K ≅ F_v` of the target,
`Langlands.Global.completionWeilTransportEquiv` composes the above equivalence
for `f.symm` with `padicFieldAtWeilEquiv v h`. Its underlying continuous
homomorphism is definitionally the target's existing
`completionWeilTransport v h K f`; the corresponding theorem records this
identity.

`completionWeilExactEquiv` applies
`ExactGrothendieckGroup.continuousRestrictEquivalence` to that equivalence.
It maps the continuous exact Grothendieck group at `F_v` to the group at `K`,
with the same arbitrary representation-carrier universe on both sides. Its
linear map is definitionally restriction along the exact completion transport
of the target. The field universes are independent as well.

This module proves transport properties only. The existence of global fields,
witnessed pairs and the image-containment conclusion of Henniart globalization
remain separate proof obligations.
