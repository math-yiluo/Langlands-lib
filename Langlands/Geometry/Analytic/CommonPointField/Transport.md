# Transport of analytic point fields

Worker 310. Derived internal infrastructure for the common analytic point field.
The definition `FieldPoint.mapField` composes all evaluations with an isometric
algebra homomorphism into another normed coefficient algebra field. The point
is preserved, the norm condition follows from the isometry, and associativity
of algebra homomorphism composition preserves the restriction identities.

The accompanying universe-lift helpers equip `ULift F` with the original normed
field structure and pass the ultrametric inequality through `down`. Completeness
of a lifted field is the existing Mathlib instance. `liftBaseNormedAlgebra`
explicitly uses the original scalar action after `down` to turn an `F`-normed
algebra into an algebra over `ULift F`. `upAlgHom` and `downAlgHom` are Mathlib's
lifted algebra equivalence in the two directions, with the original coefficients.
These constructions add no hypotheses about characteristic or nontrivial norms.
They only transport the supplied algebraic and metric structures.
