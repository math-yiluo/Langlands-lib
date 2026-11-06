# Trace pullback and additive-character scaling

This internal derived module proves that the actual field-trace pullback of an
additive character commutes with scaling by a field unit. The scalar on the larger
field is the image of the given unit under its actual inclusion, without choosing
any new scalar or trace map.

For arbitrary supplied finite p-adic topological data, `traceCharacter_scale`
uses extensionality of nontrivial unitary additive characters and linearity of
`Algebra.trace`. Multiplication by the image of a base scalar is its algebra
scalar action, so trace takes that multiplication to multiplication by the
original scalar. The continuity and nontriviality of both characters come from
the published transport constructors.

In the common algebraic closure, `trace_unitsInclusion_mul` states this scalar
identity for the algebra structure defined by `IntermediateField.inclusion h`.
The second `traceCharacter_scale` applies it pointwise to the actual
`CommonClosure.traceCharacter` and `FiniteIntermediateExtension.unitsInclusion`.
The canonical topologies are retained on both fields, and no normalized absolute
value comparison or reciprocity hypothesis is needed.

These are algebraic consequences of the existing field-trace and character
transport definitions. They supply the compatibility used when applying the
system's degree-zero induction relation at a scaled additive character.
