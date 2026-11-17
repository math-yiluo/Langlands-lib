# Group objects from uniquely lifted operations

Worker 336.

`Langlands.CategoryTheory.GroupObjectLift.grpObjOfInjective` constructs a
`GrpObj P` in an arbitrary Cartesian monoidal category from an existing
group object `X`, a morphism `j : P → X`, and specified lifts of the unit,
multiplication and inverse of `X`. The resulting operations on `P` are
definitionally those supplied. The morphism `j` must satisfy the operation
compatibilities and composition with `j` must be injective on each of
`Hom(P,P)` and `Hom((P ⊗ P) ⊗ P,P)`. No injectivity on other test objects is
assumed.

`monObjOfInjective` is the corresponding monoid construction from the unit
and multiplication. `isMonHom_grpObjOfInjective` proves that `j` preserves
the constructed group law, expressed by Mathlib's `IsMonHom` class.

For the unit laws, the proof first precomposes with the inverse of the
appropriate unitor. This changes the source of the equation to `P`, where
the given injectivity applies. Compatibility of the lifted operations
reduces the equation to the ambient unit law. Associativity follows by
injectivity on the cube and the ambient associativity equation, using
naturality of the associator. Each inverse law is checked on `P` after
composition with `j` and then follows from the ambient inverse law. The
homomorphism claim is exactly the two given compatibility equations.

This is an internal categorical derivation from the axioms in Mathlib's
`CategoryTheory.Monoidal.Grp` and its imports. It adapts the cancellation
argument of `Langlands.CategoryTheory.GroupObjectDescent` to the restricted
injectivity supplied by a normalization lifting property. This module
constructs no normalization or scheme cover and establishes no geometric
existence assertion.
