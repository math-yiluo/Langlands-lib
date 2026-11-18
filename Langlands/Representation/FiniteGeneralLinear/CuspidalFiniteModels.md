# Finite-dimensional models for cuspidal classes

Worker 666, Task 7621.

`CuspidalModelClass n k` is the subtype of ordinary irreducible complex representation classes of `GL_n(k)` whose chosen finite-dimensional representatives satisfy `IsCuspidal`. Cuspidality travels across an equivariant linear equivalence, so the choice of representative gives the same predicate on the class. This is an internal counting model derived from the Library's `CuspidalClass` and `IrreducibleClass`.

For a finite group, an irreducible complex representation is a finitely generated module over the complex group algebra by simplicity. The group algebra is finite dimensional because the group is finite. Transitivity of module finiteness gives finite dimensionality of the original representation. The Library's finite coordinate model then gives a class in the coefficient field's universe, and `ofRepresentation_eq_iff` characterizes equality of its classes by actual representation equivalence.

`equivCuspidalClass` maps the published quotient to these finite-dimensional classes over a finite field. It is injective by the class equality criterion. It is surjective because each finite-dimensional model lifts to the specified carrier universe via `ULift`, preserving irreducibility and cuspidality.
