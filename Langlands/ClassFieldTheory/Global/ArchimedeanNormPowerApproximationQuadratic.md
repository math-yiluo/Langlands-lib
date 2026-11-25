# Archimedean norm-power approximation for a quadratic extension

For a number field extension `B/F`, the approximation proposition asks
for a global pair representing any family `(b_v, s_v)` of local tensor-unit
and scalar-unit pairs with `N(b_v) = s_v^n`. The representative `(b,s)`
must satisfy `N(b) = s^n`. At every infinite place one completed tensor
unit must have `n`-th power `b/b_v` and norm `s/s_v`.

The theorem assumes a positive exponent and either quadratic degree or
degree coprime to the exponent. The Bézout construction covers coprime
degree, including quadratic degree and odd exponent. In quadratic degree
and even exponent `n = 2m`, the scalar norm is the square map, so
`b_v/s_v^m` has norm one. Quadratic tensor Hilbert 90 writes this unit
as `t_v/τ(t_v)`. Approximate the `t_v` modulo `n`-th powers by a global
`a` in `B`, and the `s_v` modulo squares by `s` in `F`. The global unit
`b = s^m a/τ(a)` has norm `s^n` by conjugation invariance. If the
local ratios are `a/t_v = q_v^n` and `s/s_v = p_v²`, then
`p_v q_v/τ(q_v)` has the desired power and norm.

This internal argument combines archimedean approximation on field units
with the determinant norm and conjugation on the actual completion tensors.
