# The positive dimension-zero coherent Euler polynomial

These internal lemmas give the base case for induction in ample Euler
positivity. Let `f : X → Spec K` be proper, with `X` noetherian and separated,
and let `M` be an actual quasi-coherent module with finite sections on every
affine open. Suppose `HasSupportDimensionLT M 1`, the published closed
support-height bound for support dimension at most zero.

`coherentEulerConstantPolynomial f M hM` is the constant rational polynomial
formed from the actual coherent Euler characteristic of `M`. Its construction
requires properness and coherence; the support bound is used to identify it
with the Euler polynomial and to prove positivity.

For any actual line bundle `L` and any natural truncation `d`,
`coherentEulerPolynomial f M hM L d` is the constant polynomial whose value is
the rational cast of the actual coherent Euler characteristic of `M`. Its
leading coefficient is strictly positive exactly when `M` is not a zero
object. In particular a nonzero such sheaf has a polynomial of natural
degree zero with positive leading coefficient. The line bundle need not
be ample.

The first lemma identifies the zeroth entry of the actual Euler sequence
with the original Euler characteristic, using the actual tensor right
unitor. Expanding the zeroth Newton truncation gives the constant polynomial;
these two lemmas require only properness and coherence. Under the support
bound, the previously proved coherent Euler polynomial evaluation theorem
identifies every truncation's values with the zeroth truncation's values.
Equality on natural arguments then determines the polynomial.

The positivity proof uses the published
`HasSupportDimensionLT.hasFiniteClosedSupport` theorem, which turns the
support bound into finite stalk support at closed points. The published
`eulerCharacteristic_pos_iff_of_finiteClosedSupport` theorem reduces actual
Euler characteristic to the dimension of zeroth cohomology, identifies it
with global sections, and detects zero sheaves with this finite support.
Proper coherent cohomology supplies its finiteness input. Positivity of the
rational cast and the leading coefficient of a constant polynomial give the
remaining assertions, including the zero-sheaf case in the equivalence.

This module derives its constant-polynomial construction and companion claims
from those published results. It introduces no positivity certificate and
makes no assertion about a positive-dimensional sheaf or the still separate
ample-positivity induction.
