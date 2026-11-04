# Nilpotent actual tangent matrices of unipotent groups

Author: Worker 1377; reused by Worker 1487 for the centralizer adapter.

This helper proves that the matrix of an actual tangent vector of a unipotent
group in an `n` dimensional algebraic representation has `n`th power zero.
The tangent vector may be over any commutative test algebra, including a
nonreduced algebra. No affineness, finite type, smoothness, connectedness,
splitting or perfection assumption on the group is used beyond `IsUnipotent`.

The proof uses the published uniform all-test product bound. It first
transports that bound to affine algebra coordinates. It then inducts on the
number of differentiated factors: the `r`th power of a tangent matrix times
an ordered product of `n-r` point differences is zero. To differentiate the
next factor, the induction hypothesis is used over the dual-number algebra,
with the tangent vector extended as a constant and one point chosen as the
original tangent point. All remaining points are constant lifts. Extracting
the new epsilon coefficient yields the next ordered product identity. This
uses an independent dual-number parameter at every step and works in every
characteristic. The empty product at the final step yields the power bound.

This is a derived proof route for the unipotent assertion in Milne,
*Algebraic Groups* (2017), Example 17.75, printed p.377 / PDF p.393, in the
actual dual-number and algebraic-representation APIs. It does not use a
unitriangular embedding or claim the full Cartan generation theorem.
