# Mellin integration by parts for real radial Schwartz tests

The Mellin integral of a real-variable Schwartz test converges for
`Re s > 0`. Boundedness controls the origin, and arbitrary polynomial
decay controls infinity. The same estimates show that `x^s f(x)` tends
to zero at both ends of the positive half-line.

`mellin_schwartz_deriv_succ` applies integration by parts with
`(x^s)' = s x^(s−1)` on that half-line. It identifies the Mellin
integral of the Schwartz derivative at `s+1` with `−s` times the
original integral at `s`. This is the scalar step for radial Mellin
continuation on products.
