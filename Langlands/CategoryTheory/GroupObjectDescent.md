# Restricting group objects along monomorphisms

This auxiliary module supplies the categorical group laws needed after restricting the actual torsion closure's operations. In a Cartesian monoidal category, `monObjOfMono` takes a monomorphism `j : P ⟶ X`, a monoid object `X`, and prescribed lifts `e` and `m` of its unit and multiplication. It constructs a monoid object on `P` with those exact operations.

`grpObjOfMono` adds a prescribed inverse map `w` satisfying `w ≫ j = j ≫ ι[X]`. Its unit, multiplication and inverse are definitionally the supplied `e`, `m` and `w`. `isMonHom_grpObjOfMono` proves that `j` preserves the resulting unit and multiplication. Finally, with a chosen braiding on the category, `commMonObjOfMono` descends commutativity along any monomorphic monoid homomorphism into a commutative monoid object.

Each law is proved by composing with `j` and cancelling this monomorphism. Compatibility of the prescribed maps, naturality of the monoidal coherence maps, and the ambient monoid or group laws then establish the required equation. The inverse laws use the Cartesian pairing identities already in Mathlib.

This is an internal categorical derivation from Mathlib's `MonObj`, `GrpObj`, `IsMonHom` and `IsCommMonObj` axioms, implemented in `Mathlib.CategoryTheory.Monoidal.Grp` and its imports. Worker 306 supplied this helper for the coauthored actual torsion-closure group-scheme proof. It supplies no geometric factorization, smoothness, dimension, torsion count, or density result.
