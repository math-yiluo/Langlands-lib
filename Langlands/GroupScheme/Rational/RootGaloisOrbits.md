# Actual root Galois orbits and their stabilizer fields

This internal construction applies the published ordinary Galois transport
of actual adjoint weights and the published finite-Galois orbit/embedding
correspondence. The field `k`, its extension `L`, and the actual group
schemes have arbitrary universe `u`.

For an actual morphism `j : T.toGrp ⟶ G` over `k`, with `G` affine,
`rootsGaloisAction` restricts the ordinary character Galois representation
to the actual roots of `j_L`. Root preservation is the existing
`mem_roots_galois_iff`; the representation identities prove the action
identities. The action is a named, instance-reducible definition, installed
locally in this module; consumers can install the same definition locally.
No chosen root datum, reductivity assumption, or premise about
root-group coordinates is needed.

`rootOrbitField k L j β` is the intermediate field fixed by the stabilizer
of the actual root `β`. The membership theorem expresses that stabilizer
using equality in the actual character lattice. If `L/k` is finite Galois,
`rootOrbitEmbeddingEquiv` identifies the actual root's Galois orbit with the
`k`-embeddings of this field in `L`. Postcomposition of embeddings
corresponds to the same ordinary Galois action on roots. These equivalence
proofs reuse `FiniteGaloisOrbits`.

For a descended commutative-group morphism `f : S ⟶ T`,
`rootRestrictionFiber k L j f a` consists of actual roots of `j_L` whose
restriction along `f_L` equals the base change of the original character
`a`. Restriction commutes with ordinary Galois transport, and the base
change of `a` is Galois fixed. This proves that each fiber is stable and
that the orbit of any of its roots is contained in the fiber.

When `S` is split, `T_L` is split, and `G` is locally of finite type,
the published `splittingFieldRootLift` gives a member of the fiber for
each actual root of `f ≫ j`. The last theorem therefore supplies one
actual Galois root orbit contained in each such fiber. These fiber
results hold even when `L/k` is not finite Galois; that condition is only
needed for the embedding equivalence.

The provenance is internal, by specialization of the existing character
transport, root-lifting, and stabilizer-field constructions. Containment
of an orbit in a restriction fiber does not assert that the fiber is one
orbit. The module does not prove quasi-split R1 fiber transitivity,
trivialize root lines, identify an actual relative root group with the
additive group of the stabilizer field, or construct apartment data.
