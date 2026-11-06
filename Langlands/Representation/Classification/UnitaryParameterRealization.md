# Actual unitary parameter realizations

Author: Worker 1431. Derived finite construction.

This pair packages actual inducing parameters for a prescribed smooth
representation and assembles finite products of supplied realizations. It is
an internal construction from `UnitaryGenericStatement` and
`UnitaryParameterFlattening`. It does not assert that arbitrary unitary or
generic representations admit such parameters.

Fix an arbitrary prime `p`, `F : PadicField.{uF} p`, and compatible topology
`T`. The field and representation universes remain independent, and every
representation has its actual carrier in `Type (max uF uV)`. All products use
the existing normalized standard upper-block induction, with its actual
topology, external tensor product, and group action.

For an actual smooth representation `π` of `GL_n(F)`,
`UnitaryParameterRealization F T π` stores the following data:

- A `BlockShape n`, with positive block ranks and total rank `n`.
- An actual smooth representation of each block group and one real exponent
  for each occurrence.
- The exact predicate `IsUnitaryGenericDatum` on that family.
- A categorical isomorphism from `π` to the entire
  `T.twistedProductInduced` of that family.

The validity field includes irreducibility, an invariant positive Hermitian
form, and analytic square-integrability of every block, both strict
inequalities `-1/2 < s i < 1/2`, and multiplicity-preserving Hermitian
parameter symmetry with actual transported block isomorphisms. The structure
stores witnesses of these existing conditions; it neither weakens the
conditions nor creates them for arbitrary `π`. It makes no genericity or
unitarizability assertion about `π` itself.

`UnitaryParameterRealization.ofIso` pulls a realization for `σ` back along a
given isomorphism `π ≅ σ`, composing that isomorphism with the stored
comparison. `rankTransport` transports a realization along an exact equality
of total group ranks. Its proof eliminates the rank equality, retaining all
stored data. `exists_datum` forgets the choices and provides the corresponding
existential statement, including nonemptiness of the actual isomorphism type.

For a block shape `B : BlockShape n`, an actual block family `σ`, and a
realization `R j` of every `σ j`, `exists_unitaryProductParameters` supplies
valid parameters for the whole object
`(T.normalizedProductInductionFunctor B).obj σ`. The proof first treats the
inner shapes, block families, exponent families, validity proofs, and local
isomorphisms as independent arguments. It concatenates these parameters in
the exact ordered refinement coordinates. The theorem
`isUnitaryGenericDatum_flatten` retains every block condition, strict bound,
and occurrence in the Hermitian matching.

For the representation comparison, the family of local isomorphisms is an
isomorphism in the product category. Applying the outer normalized-product
functor gives an isomorphism from the whole product of the `σ j` to the
nested product of their realized inner products. Composing with the inverse
of `flattenedUnitaryProductIso` gives the required direction from that
original product to the flattened twisted product. Specializing the
independent arguments to the fields of `R j` completes the existential
assembly theorem.

`UnitaryParameterRealization.product` packages the assembled parameters and
an actual comparison as a realization of the entire normalized product.
Its private existence proof eliminates the preceding existential statement
inside `Nonempty`. Classical choice then selects the stored data and map.
No evaluation formula or uniqueness claim is made for this choice.

This derivation needs no new literature assertion. The only mathematical
inputs beyond the stored local realizations are the existing parameter
predicates, ordered flattening construction, and functoriality of normalized
induction. It applies to arbitrary total rank, including the empty block
family at rank zero. It supplies no local realization from classification,
no genericity elimination, and no proof of `UnitaryGenericExhaustion` or
parameter uniqueness.
