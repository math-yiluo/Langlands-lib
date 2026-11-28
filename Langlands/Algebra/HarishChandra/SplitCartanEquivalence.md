# Transport of a split Cartan subalgebra along a Lie equivalence

A complex Lie equivalence carrying one subalgebra onto another restricts
to a linear equivalence of adjoint weight spaces. The source weight is
the pullback of the target weight by the restricted Lie equivalence on
the two subalgebras. `LieEquiv.weightSpaceEquiv` implements this
restriction. The weight equations correspond because the two Lie
equivalences preserve the bracket and scalar action.

`IsSplitCartan.map` transports the conditions of `IsSplitCartan` from
`ParabolicIndependenceStatement`. A weight on the source subalgebra
comes from a weight on the target by using the inverse equivalence.
The images of the source weight spaces therefore span the target Lie
algebra, and the zero weight space maps to the image subalgebra. The
weight space equivalence preserves dimension. The Lie equivalence carries
the opposite-root vectors and their bracket to the target and preserves
the weight value at that bracket. Pullback preserves nonvanishing and
commutes with scalar multiplication, giving reducedness from the source
subalgebra.
