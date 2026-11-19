# Multiplicity-free finite representations

`ConstituentClass V` is the subtype of irreducible complex representation classes with a positive-dimensional space of intertwiners from `V`. It is an internal representation-counting type defined using the Library's finite representation models. For a finite group, character
orthogonality makes the irreducible characters linearly independent in the
finite-dimensional space of functions on the group. This gives finiteness of the
irreducible classes and the constituent subtype.

For a finite group, take an internal direct sum decomposition into irreducible subrepresentations. Each summand has an equivariant inclusion and projection. If two distinct summands were equivalent, their off-diagonal intertwiner and the projection onto its source would have different products in the two orders. Thus commuting endomorphisms imply that the classes of the summands are distinct.

The trace of the internal direct sum is the sum of the summand traces. Character orthogonality shows that the intertwining dimension from `V` to an irreducible is one if its class occurs among the summands and zero otherwise. The dimension of the endomorphism space is the sum of these dimensions over the summands, so it is the cardinality of `ConstituentClass V`.
