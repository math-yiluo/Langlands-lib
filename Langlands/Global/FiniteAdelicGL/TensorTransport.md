# Arithmetic transport of finite adelic tensor representations

This internal construction uses actual number fields `K` and `L` in independent
universes, an isomorphism `a : K ≃+* L`, an independently quantified coefficient
field `A`, and arbitrary local `A`-modules. No dimension or topology on those
modules is imposed.

Let `q = finitePlaceEquiv a`, the existing ideal-comap equivalence from finite
places of `L` to those of `K`. `transportFactors a ρ` at `v` acts on `V(q v)` by
precomposing `ρ(q v)` with the inverse of the actual completion-group
isomorphism `localEquiv n a v`. `transportExceptional a E` is `E.map q.symm`.
The proved image identity returns exactly `E`. The pulled-back reference vector
at `v` is `e(q v)`; integrality preservation and reflection for matrices and
inverses proves `transportReference_fixed` outside the new exceptions.

`tensorTransportEquiv` is a genuine representation equivalence from the
transported finite adelic tensor representation, precomposed with the actual
`finiteEquiv n a`, to the original tensor representation. It requires the
original integral fixedness and nonzero references outside `E`.

The proof first uses the actual linear reindexing equivalence with an arbitrary
new exceptional set and its image. The existing projection identity for
arithmetic matrix transport shows that the local operators on the transported
tensor are exactly the pulled-back old operators. The proved factor-map
naturality of restricted tensor reindexing supplies covariance. Finally the
exceptional-set image identity yields the stated exact original exceptions.
All spaces are the existing algebraic tensor direct limits and all group maps
are the existing arithmetic completion and adelic maps.

This is a derived composition of existing Library constructions and introduces
no new identification with original literature. It assumes no desired tensor
comparison, factorization, automorphic occurrence, smoothness or spectral
existence assertion.
