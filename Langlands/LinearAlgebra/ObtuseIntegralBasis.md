# Short vectors in an obtuse even integral lattice

`IsEvenIntegralOn B L` states that a real bilinear form takes integer
values on every pair of elements of the integer submodule `L`, and
that the squared length of every element of `L` is twice an integer.
For a symmetric form, integral pairings of generators and even squared
lengths of generators suffice. The proof uses integer-span induction
in each argument, and then integer-span induction on the diagonal.
The addition step uses symmetry to make the cross term twice an
integer. Every positive squared length in such a lattice is at least
two.

The finite-family result considers a real linearly independent family
whose integer span is even integral, with pairwise nonpositive
off-diagonal pairings in a positive definite symmetric form. An
integer combination of squared length two has all its coefficients
nonnegative or all nonpositive. The proof splits the coefficients into
positive and negative parts. If both signs occur, independence makes
both resulting vectors nonzero. Each has squared length at least two;
their mutual pairing is nonpositive because the coefficient supports
are disjoint and the family is obtuse. Their difference would have
squared length at least four, contradicting the assumed length two.

This is internal linear-algebra infrastructure for the finite-base
step of the local anisotropic affine-diagram task. It does not assume
or construct an algebraic group or a root system, and it asserts no
classification or absolute Cartan comparison. The module is derived
from bilinearity, integer-span closure, positivity, and independence,
not transcribed from a literature statement.
