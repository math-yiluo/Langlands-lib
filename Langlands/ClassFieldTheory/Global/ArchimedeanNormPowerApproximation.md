# Archimedean approximation of norm-power pairs

The scalar-unit map is induced by the right tensor inclusion. Its norm
is the power by the extension degree. A base-field unit has the same
image from either tensor factor by the balancing relation.

For each infinite place of a number field extension `B/F`, take the
coordinate of the supplied tensor unit at the restriction of that place.
Weak approximation modulo powers on `B` gives a global unit `t` and
local roots of its ratios to those coordinates. The completed tensor-unit
equivalence assembles the roots over each place of `F`.

Suppose the supplied pairs `(b_v, s_v)` satisfy `N(b_v) = s_v^n`, where
`n` is positive and coprime to the extension degree `d`. Choose integers
`a, c` with `d*a + n*c = 1`. Set `T = N(t)`, `b = t/T^a`, and `s = T^c`,
using the scalar image in `B` for the denominator. The norm of a scalar
is its `d`-th power, so `N(b) = s^n`. If `q_v` is the original local
root of `t/b_v`, put `h_v = s_v*N(q_v)`, so `T = h_v^n` in the base
completion. The unit `q_v/h_v^a` has `n`-th power equal to `b/b_v` and
norm equal to `s/s_v`.

This internal construction provides the simultaneous archimedean unit
and norm comparisons used to correct a lifted norm-one torsion cocycle.
