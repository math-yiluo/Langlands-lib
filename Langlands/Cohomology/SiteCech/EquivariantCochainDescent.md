# Primitives from equivariant three-term models

This internal construction isolates the categorical step needed for descent of
finite fixed Čech cocycles. Let `P` be an ordinary chain complex, `V : E ⥤ D` a
faithful functor preserving zero morphisms, and `I` an object of the abelian
category `E`. A supplied isomorphism identifies `V.obj I` with the ordinary
coefficient `F`.

`EquivariantCochainLift` contains an exact short complex in `E`. Its ordinary
middle and lower terms are isomorphic to `P.X (n + 1)` and `P.X n`. A map from its
ordinary upper term to `P.X (n + 2)`, and both differential squares, identify its
two differentials with the actual differentials of `P`. Finally, a morphism
from its middle term to `I` lifts the specified ordinary cochain `x`.

If `x` is a cocycle, the upper square and faithfulness of `V` show that its lift
annihilates the first differential. When `I` is injective,
`ShortComplex.Exact.descToInjective` provides a primitive in `E`.
`EquivariantCochainLift.primitive` transports it using the lower-term
isomorphism and the coefficient isomorphism. The lower square proves
`comp_primitive`, identifying its differential with `x`.

This is a source-free internal derivation from the existing Mathlib exact
short-complex and injective-object APIs. It supplies no geometric model,
equivariant lift, or unconditional exactness assertion. In the intended analytic
application those remain obligations for the finite lifted Čech nerve.
