# Finiteness of the nonsplit finite places

For a finite-dimensional central simple algebra \(A\) over a number
field \(F\), `Langlands.Brauer.nonsplitFinitePlaces A` is the set of
finite places \(v\) where \(F_v\otimes_F A\) has no matrix chart of
positive size. The theorem `finite_nonsplitFinitePlaces` proves this
set is finite.

Choose a finite Galois splitting field and take the principal idele
image of the relative Brauer class of the splitting chart. Its finite
local support is finite by the local invariant image laws. If a
place is outside that support, the field-unit localization at a
chosen place above it is zero. The local chart compatibility turns
that vanishing into a matrix chart over the completion. This
places every nonsplit finite place in the finite support.

This is the finite-place support consequence of Platonov and
Rapinchuk, *Algebraic Groups and Number Theory* (1994), §1.5.1,
Theorem 1.12, p. 38.
