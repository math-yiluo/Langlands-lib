# Filtered spanning after removing stable Lie directions

Author: Worker 94. This internal algebraic consequence of the filtered retraction
comparison concerns a field `R : Type`, a Lie algebra in any universe, and any
genuine universal-enveloping module with its compatible `R`-scalar action.

`retractedSymmetrizationSpan f d` is the image of the actual symmetric monomial
span of length at most `d`, first under the algebra homomorphism induced by the
linear endomorphism `f` and then under whole symmetrization. These images increase
with `d`, contain the unit, and lie in the genuine enveloping degree piece `F_d`.

Let `M` contain every vector `X - f X`, and let the subspace `W` be preserved by
every enveloping generator of a vector of `M`. In characteristic zero the theorem
`retractedSymmetrizationSpan_smul_eq` proves that the action span of the retracted
symmetric image on `W` equals `F_d W`, for each degree `d`. No idempotence of `f`,
PBW injectivity, finite dimension, or topology is assumed.

The proof inducts on `d`. At degree zero, the genuine enveloping filtration is
the constants, and the retracted symmetric image contains the unit. For a product
`a • w` in the next action span, filtered surjectivity supplies a bounded whole
symmetric preimage of `a`. The previously proved comparison places the difference
from its retracted symmetrization in the remainder with coefficient degree `d`.
Stability of `W` absorbs the rightmost removed generator. The induction hypothesis
includes this lower filtered action span in the retracted symmetrization span;
monotonicity puts it in the desired next span. Adding the retracted main term
recovers `a • w`, and additivity gives the whole action span.

This proves filtered algebraic spanning only. Actual Cartan specialization,
compact covariant lifting, central finite generation and automorphic derivative
growth require further arguments.
