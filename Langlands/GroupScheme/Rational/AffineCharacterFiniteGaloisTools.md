# Finite coefficient models of tensor units

Author: Worker 706; verified and documented for the exact descent proof by
Worker 1366. These are derived internal algebraic tools, with no claim to
reproduce a particular external source.

Let `k K : Type u` be fields with `Algebra k K` and `IsGalois k K`, and let
`A : Type u` be any commutative `k`-algebra. The extension `K/k` may have
infinite degree, and `A` need not be finitely generated.

`tensorEmbed A E` is the algebra map `E ⊗[k] A →ₐ[k] K ⊗[k] A` induced by
the intermediate-field inclusion and the identity of `A`.
`tensorEmbed_inclusion` says that enlarging the finite coefficient field and
then embedding gives the original embedding.

`exists_tensorEmbed_eq` proves that every tensor lies in the image of one
such finite Galois coefficient field. The proof uses tensor induction. A pure
tensor uses `FiniteGaloisIntermediateField.adjoin k {c}`, which adjoins a
finite Galois field containing its extension coefficient. An addition uses
the supremum of the two finite Galois intermediate fields and maps both
summands into it. This is a finite coefficient argument, independent of the
number of generators of `A`.

`tensorEmbed_injective` applies `TensorProduct.map_injective_of_flat_flat`
to the injective field inclusion and the identity linear map of `A`.
Modules over the field `k` are flat. This injectivity and the inclusion
compatibility do not require the ambient `IsGalois k K` instance.

Finally, `exists_tensorEmbed_unit` applies the tensor lemma to the value of
a unit and to its inverse. Both models map into the supremum of their finite
Galois fields. Injectivity reflects their product equation; commutativity
gives the reverse product equation. These elements therefore define a unit
whose image is the original unit, as asserted by equality of units.
