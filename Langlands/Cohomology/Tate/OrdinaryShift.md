# Ordinary cohomology dimension shifting

Author: Worker 45.

`ordinaryShiftUpDelta A n` is Mathlib's actual connecting map from
`H^n(G, shiftUp A)` to `H^(n+1)(G,A)`, for the published exact sequence
from `A` into its coinduced replacement and then its cokernel `shiftUp A`.
It is surjective for every natural `n`. For positive `n`,
`ordinaryShiftUpIso A n` equips this same map with a proved inverse.
There is no assertion of invertibility when `n = 0`.

The implementation transports the published vanishing of Tate cohomology of a
coinduced coefficient through Mathlib's positive ordinary comparison. Thus the
middle ordinary cohomology term vanishes in every positive degree. The ordinary
long exact sequence supplies surjectivity of the connecting map, and also
injectivity when its source degree is positive. `asIso` constructs the inverse
from those proved properties.

`ordinaryClass_shift_induction` reduces any predicate on ordinary classes to
invariant-vector representatives in degree zero and preservation by these
connecting maps. Its proof is induction on the natural degree, lifting each
successor class through the established surjection. In degree zero it uses
Mathlib's `H0Iso` to represent the class by an invariant vector.
`ordinaryClasses_shift_induction` applies the same reduction to two classes:
first reduce the second degree, then the first with the second fixed at zero.
The hypotheses are an explicit induction scheme; they neither define a cup
product nor assert that any particular operation satisfies compatibility laws.

This construction and its induction certificates are internal consequences of
the published `ShiftDefinitions`, `Coinduced`, and Mathlib's ordinary long exact
sequence. They prepare the comparison with independently constructed ordinary
cochain products. The files use an arbitrary common universe `u`, commutative
scalar ring `R`, and finite group `G`. No tensor exactness or flatness hypothesis
is required.
