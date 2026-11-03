# Finite adapted bases

This internal field-linear construction supplies the coordinate choice in
the Chevalley stabilizer argument. For any subspace of a finite-dimensional
vector space, it constructs one finite basis of the ambient space and an
increasing selection of basis indices spanning that subspace.

The proof chooses a complementary subspace, takes finite bases of the two
summands, transports their product basis through the direct-sum linear
equivalence, and reindexes the sum of finite index sets by `Fin`. Expansion
in the basis of the first summand proves the claimed equality of actual
submodules. There is no assumption on the dimension or codimension of the
chosen subspace.

`exists_adapted_subspace_basis` applies this inside a finite-dimensional
subspace of an arbitrary ambient vector space and maps the span equality
through its genuine subtype inclusion. Only the containing subspace must
be finite dimensional.
